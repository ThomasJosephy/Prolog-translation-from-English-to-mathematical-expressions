:- use_module( [library(lists),library( clpfd )] ).

:- assert( clpfd:full_answer ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 1. DEFINITE CLAUSE GRAMMAR (You may modify these subsections as needed)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%-----------------------------------------------------------------------------
% a. PARSING HIGH-LEVEL SENTENCES
%-----------------------------------------------------------------------------

% lpsolve(+Data, -Answers)
% front end: lpsolve/2 succeeds when its first
% argument is a list of well formed sentences
% and its second is a list of constrained variables
lpsolve( Data, Answers ) :-
    lpsolve( [], Answers, Data, [] ).

% lpsolve/4 succeeds when its first argument is a
% list of variable name/Prolog variable pairs, its
% second is the same list modified with any new
% variables introduced in the list of sentences
% in argument 3 which is parsed with the remainder
% given in argument 4
% lpsolve(+VariablesIn, -VariablesOut)
lpsolve( VariablesIn, VariablesOut ) -->
    sentence( VariablesIn, VariablesOut ).

lpsolve( VariablesIn, VariablesOut ) -->
    sentence( VariablesIn, VariablesBetween ),
    lpsolve( VariablesBetween, VariablesOut ).

% sentence(+VariablesIn, -VariablesOut)
% Parse a sentence and return a list of variable name/Prolog variable pairs. 
% This one is for when a variable is in a domain but not a single value AND we talk about a variable defined previously.
sentence( VariablesIn, VariablesOut ) -->
    word_it,
    range_keyword,
    factor(FirstBound, VariablesIn, _),
    separator_keyword,
    factor(SecondBound, VariablesIn, _),
    {
        look_up(word_it, VariablesIn, VariablesOut, Subject),
        bounds_sorted(FirstBound, SecondBound, Min, Max),
        Subject in Min..Max
    },
    [fullstop].

% This one is for when a variable is an inequality AND we talk about a variable defined previously
sentence( VariablesIn, VariablesOut ) -->
    word_it,
    range_operants(Op),
    plus_and_minus(Expr, VariablesIn, _),
    {
        look_up(word_it, VariablesIn, VariablesOut, Subject),
        Constraint =.. [Op, Subject, Expr],
        Constraint
    },
    [fullstop].

% This one is for when a variable have a unique value AND we talk about a variable defined previously
sentence( VariablesIn, VariablesOut ) -->
    word_it,
    eq_operants(_),
    plus_and_minus(Expr, VariablesIn, _),
    {
        look_up(word_it, VariablesIn, VariablesOut, Subject),
        Subject #= Expr
    },
    [fullstop].

% This one is for sentences that restrict every previous variable in a domain
sentence( VariablesIn, VariablesOut ) -->
    word_all,
    word_variable,
    range_keyword,
    factor(FirstBound, VariablesIn, _),
    separator_keyword,
    factor(SecondBound, VariablesIn, _),
    {
        look_up(word_all, VariablesIn, VariablesOut, _),
        bounds_sorted(FirstBound, SecondBound, Min, Max),
        apply_range_constraint(VariablesIn, Min, Max)
    },
    [fullstop].

% This one doe sthe others constraint on every variables defined previously
sentence( VariablesIn, VariablesOut ) -->
    word_all,
    word_variable,
    range_operants(Op),
    plus_and_minus(Expr, VariablesIn, _),
    {
        look_up(word_all, VariablesIn, VariablesOut, _),
        apply_operation_constraint(VariablesIn, Op, Expr)                               
    },
    [fullstop].

% This one is for when a variable is in a domain
sentence( VariablesIn, VariablesOut ) -->
    variable_subject(Name, Type),
    { 
        check_scope(Name, Type, VariablesIn) 
    },
    range_keyword,
    factor(FirstBound, VariablesIn, Var1),
    separator_keyword,
    factor(SecondBound, Var1, Var2),
    { 
        look_up(Name, Var2, VariablesOut, Var), 
        bounds_sorted(FirstBound, SecondBound, Min, Max), 
        Var in Min..Max 
    },
    [fullstop].

% This one is for when a variable have a precise value
sentence( VariablesIn, VariablesOut ) -->
    variable_subject(Name, Type),
    { check_scope(Name, Type, VariablesIn) },
    eq_operants(_),
    plus_and_minus(Term, VariablesIn, VariablesTemp),
    { look_up(Name, VariablesTemp, VariablesOut, Var), Var #= Term },
    [fullstop].

% This one is for when a variable is an inequality.
sentence(VariablesIn, VariablesOut) -->
    variable_subject(Name, Type),
    { check_scope(Name, Type, VariablesIn) },
    range_operants(Op),
    plus_and_minus(Expr, VariablesIn, VariablesTemp),
    { look_up(Name, VariablesTemp, VariablesOut, Var), Restriction =.. [Op, Var, Expr], Restriction },
    [fullstop].

% range_keyword
range_keyword --> [lies, between].
range_keyword --> [is, between].
range_keyword --> [are, between].
range_keyword --> [is, in, the, range].
range_keyword --> [varies, from].

% range_operants(-Op)
range_operants(#>) --> [is, greater, than].
range_operants(#>) --> [are, greater, than].
range_operants(#<) --> [is, less, than].
range_operants(#<) --> [are, less, than].
range_operants(#>=) --> [is, greater, than, or, equal, to].
range_operants(#>=) --> [are, greater, than, or, equal, to].

% variable_subject(-Name, -Type)
% Important for "The" and "A" ("A variable" always introduce a new variable, otherwise it's an error).
variable_subject(Name, new) --> determiner(new), word_variable, variable_name(Name).
variable_subject(Name, known) --> determiner(known), word_variable, variable_name(Name).
variable_subject(Name, known) --> word_variable, variable_name(Name).
variable_subject(Name, known) --> variable_name(Name).

% bounds_sorted(+First, +Second, -Min, -Max)
% Sorts the bounds to avoid error if they are not in order
bounds_sorted(First, Second, Min, Max) :-
    integer(First),
    integer(Second),
    Min is min(First, Second),
    Max is max(First, Second).

% apply_range_constraint(+List, +Min, +Max)
% Apply the range constraint to every variable
% Base case
apply_range_constraint([], _Min, _Max).

% Get the pair with "all" out
apply_range_constraint([var_pair(word_all, _) | Rest], Min, Max) :-
    apply_range_constraint(Rest, Min, Max).

% Other cases
apply_range_constraint([CurrentPair | RestOfList], MinValue, MaxValue) :-
    CurrentPair = var_pair(Name, VariableValue),
    Name \= word_all,
    VariableValue in MinValue..MaxValue,
    apply_range_constraint(RestOfList, MinValue, MaxValue).

% apply_operation_constraint(+List, +Operator, +Expression)
% Apply the operation constraint to every variable (the inequalities, etc.)
% Base case
apply_operation_constraint([], _Operator, _Expression).

% Get the pair with "all" out
apply_operation_constraint([var_pair(word_all, _) | Rest], Operator, Expression) :-
    apply_operation_constraint(Rest, Operator, Expression).

% Other cases
apply_operation_constraint([CurrentPair | RestOfList], Operator, Expression) :-
    CurrentPair = var_pair(Name, Var),
    Name \= word_all,
    Constraint =.. [Operator, Var, Expression],
    Constraint,
    apply_operation_constraint(RestOfList, Operator, Expression).

% check_scope(+Name, +Type, +VarsIn)
% Check if new variables already exist, and known ones don't.
check_scope(Name, new, VarsIn) :-
    member(var_pair(Name, _), VarsIn),
    throw(error(scoping_error(Name), 'Variable already declared')).

% New variable
check_scope(Name, new, VarsIn) :-
    \+ member(var_pair(Name, _), VarsIn).

% Base case
check_scope(_, known, _).

%-----------------------------------------------------------------------------
% b. PARSING MATHEMATICAL EXPRESSIONS
%-----------------------------------------------------------------------------

% plus_and_minus(-Result, +VariablesIn, -VariablesOut)
% Parses addition and subtraction operations.
% Send first to multiplication and division to respect the order
plus_and_minus(Results, VariablesIn, VariablesOut) -->
    mult_and_div(Term1, VariablesIn, VariablesTemp),
    plus_and_minus_rest(Term1, Results, VariablesTemp, VariablesOut).

% plus_and_minus_rest(+Term1, -Results, +VariablesIn, -VariablesOut)
% Answer for the addition and substraction.
plus_and_minus_rest(Term1, Results, VariablesIn, VariablesOut) -->
    add_sub_operants(Op),
    mult_and_div(Term2, VariablesIn, VariablesTemp),
    { SumTerm =.. [Op, Term1, Term2] },
    plus_and_minus_rest(SumTerm, Results, VariablesTemp, VariablesOut).

% Base case
plus_and_minus_rest(Expr, Expr, Variables, Variables) --> [].

% mult_and_div(-Result, +VariablesIn, -VariablesOut)
% Parses multiplication and division operations
mult_and_div(Results, VariablesIn, VariablesOut) -->
    factor(Fact1, VariablesIn, VariablesTemp),
    mult_and_div_rest(Fact1, Results, VariablesTemp, VariablesOut).
    
% mult_and_div_rest(+Factor1, -Results, +VariablesIn, -VariablesOut)
% Answer for the multiplication and division
mult_and_div_rest(Factor1, Results, VariablesIn, VariablesOut) -->
    times_div_operants(Op),
    factor(Factor2, VariablesIn, VariablesTemp),
    { Product =.. [Op, Factor1, Factor2] },
    mult_and_div_rest(Product, Results, VariablesTemp, VariablesOut).

% Base case
mult_and_div_rest(Term, Term, Variables, Variables) --> [].

% factor(-Factor, +VariablesIn, -VariablesOut)
% Parses the factors
% Read an Int
factor(N, Variables, Variables) -->
    integer_number(N).

% Read a variable
factor(Var, VariablesIn, VariablesOut) -->
    variable_name(Name),
    { look_up(Name, VariablesIn, VariablesOut, Var) }.

% Read a multiplication
factor(A * B, VariablesIn, VariablesOut) -->
    [the, product, of],
    factor(A, VariablesIn, VariablesTemp),
    [and],
    factor(B, VariablesTemp, VariablesOut).

% Read a division
factor(A div B, VariablesIn, VariablesOut) -->
    [the, quotient, of],
    factor(A, VariablesIn, VariablesTemp),
    [and],
    factor(B, VariablesTemp, VariablesOut).

% Read a division
factor(A div B, VariablesIn, VariablesOut) -->
    [the, dividend, of],
    factor(A, VariablesIn, VariablesTemp),
    [and],
    factor(B, VariablesTemp, VariablesOut).

%-----------------------------------------------------------------------------
% c. PARSING LOW-LEVEL ATOMS
%-----------------------------------------------------------------------------

% add_sub_operants(-Op)
add_sub_operants(+) --> [+].
add_sub_operants(+) --> [plus].
add_sub_operants(-) --> [-].
add_sub_operants(-) --> [minus].

% times_div_operants(-Op)
times_div_operants(*) --> [*].
times_div_operants(*) --> [times].
times_div_operants(div) --> [/].
times_div_operants(div) --> [divided, by].

% eq_operants(-Op)
eq_operants(=) --> [equals].
eq_operants(=) --> [=].
eq_operants(=) --> [is, equal, to].
eq_operants(=) --> [is].
eq_operants(=) --> [contains].
eq_operants(=) --> [holds].

% determiner(-Type)
determiner(known) --> [the].
determiner(known) --> ['The'].
determiner(new) --> [a].
determiner(new) --> ['A'].

% word_variable
word_variable --> [variable].
word_variable --> [variables].
word_variable --> ['Variable'].
word_variable --> [these, variables].

% separator_keyword
separator_keyword --> [and].
separator_keyword --> [to].

% word_all
word_all --> [all].
word_all --> ['All'].

% word_it
word_it --> [it].
word_it --> ['It'].

% integer_number(-N)
integer_number(N) -->
    [N],
    { integer(N) }.

% variable_name(-Name)
% Check that a variable name is valid (1 letter, no digit)
variable_name(Name) -->
    [Name],
    {
      atom(Name),
      atom_length(Name, 1),
      \+ char_type(Name, digit)
    }.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 2. VARIABLE HANDLING PREDICATES
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% look_up(+word_it, +VariablesIn, -VariablesOut, -Boolean)
look_up(word_all, VariablesIn, VariablesOut, _Boolean) :-
    extract_var(word_all, VariablesIn, TempList, _),
    append([var_pair(word_all, true)], TempList, VariablesOut).

look_up(word_it, VariablesIn, VariablesOut, Subject) :-
    extract_var(word_all, VariablesIn, TempList, AllStatus),
    verify_it_status(AllStatus, TempList, VariablesOut, Subject).

% look_up(+Name, +VariablesIn, -VariablesOut, -Boolean)
% Check if a variable exist: if she does, we extract her. Otherwise, we create her. In both cases we append her at the end of the list to keep a track of the previous variable seen.
look_up(Name, VariablesIn, VariablesOut, Var) :-
    Name \= word_all,
    Name \= word_it,
    extract_var(word_all, VariablesIn, TempList, _),
    extract_var(Name, TempList, NewTempList, Var),
    append([var_pair(word_all, false)], NewTempList, NewTempList2),
    append(NewTempList2, [var_pair(Name, Var)], VariablesOut).

% extract_var(+Name, +VariablesIn, -VariablesOut, -Var)
% Base case
extract_var(_Name, [], [], _Var).

% Extract the variable.
extract_var(Name, [var_pair(Name, Var) | Rest], Rest, Var).

% Move her to the end of the list.
extract_var(Name, [Head | Rest], [Head | RestOut], Var) :-
    Head = var_pair(Name2, _),
    Name \= Name2,
    extract_var(Name, Rest, RestOut, Var).

% verifier_status_it(+Status, +TempList, +VariablesOut, -Subject)
% Check if "it" is used after an "all" block
verify_it_status(Status, _TempList, _VariablesOut, _Subject) :-
    Status == true,
    throw(error(scoping_error(word_it), 'Cannot use "it" after an "all" block')).

% "it" is not used after an "all" block
verify_it_status(Status, TempList, VariablesOut, Subject) :-
    Status \== true,
    append([var_pair(word_all, false)], TempList, VariablesOut),
    last(TempList, var_pair(_Name, Subject)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 3. CONSTRAINT HANDLING PREDICATES (only if needed for your implementation)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Not Used

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 4. ANALYSING THE RESULTS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% analyse(+Variables, +Residue)
% Check for infinite domains (here it's the case when they exists.), print out variables and surviving constraints.
analyse(VariablesIn, _Residue) :-
    check_infinite(VariablesIn),
    format('There may be an infinite number of solutions.~n', []).

% Finite domains
analyse(VariablesIn, _Residue) :-
    \+ check_infinite(VariablesIn),
    print_variables(VariablesIn),
    copy_term(VariablesIn, VariablesOut, Goals),
    print_surviving_constraints(VariablesOut, Goals).

% check_infinite(+List)
% Removes the first case
check_infinite([var_pair(word_all, _)|Rest]) :-
    check_infinite(Rest).

% Check for infinite domains for every variables, recursively.
check_infinite([var_pair(Name, Variables)|_Rest]) :-
    Name \= word_all,
    fd_size(Variables, sup).

check_infinite([Head|Rest]) :-
    Head = var_pair(Name, Variables),
    Name \= word_all,
    \+ fd_size(Variables, sup),
    check_infinite(Rest).

% print_variables(+List)
% Print variables, recursively.
% Base case
print_variables([]).

% We ignore 'word_all'
print_variables([var_pair(word_all, _) | Rest]) :-
    print_variables(Rest).

print_variables([HeadPair|Rest]) :-
    HeadPair = var_pair(Name, _),
    Name \= word_all,
    print_one_variable(HeadPair),
    print_variables(Rest).

% print_one_variable(+Pair)
% Print an element in particular
% Int
print_one_variable(var_pair(Name, Value)) :-
    integer(Value),
    format('~w = ~w~n', [Name, Value]).

% Others
print_one_variable(var_pair(Name, Value)) :-
    \+ integer(Value),
    fd_dom(Value, Domain),
    format('~w in ~w~n', [Name, Domain]).

% print_surviving_constraints(+Variables, +Constraints)
% Iterates through remaining constraints and prints them
print_surviving_constraints(_VariablesIn, []).

print_surviving_constraints(VariablesIn, [Constraint | Rest]) :-
    format('Constraint Pending : ', []),
    print_single_constraint(Constraint, VariablesIn),
    format('~n', []),
    print_surviving_constraints(VariablesIn, Rest).

% print_single_constraint(+Term, +Variables)
% Print an element in particular in these constraints.
% Variables
print_single_constraint(Term, VariablesIn) :-
    var(Term),
    find_name(Term, VariablesIn, Name),
    format('~w', [Name]).

% Atoms
print_single_constraint(Term, _VariablesIn) :-
    atomic(Term),
    format('~w', [Term]).

% Binary Operations
print_single_constraint(Term, VariablesIn) :-
    compound(Term),
    Term =.. [Op, Arg1, Arg2],
    print_single_constraint(Arg1, VariablesIn),
    format(' ~w ', [Op]),
    print_single_constraint(Arg2, VariablesIn).

% Base case
print_single_constraint(Term, _VariableList) :-
    compound(Term),
    \+ (Term =.. [_, _, _]), 
    format('~w', [Term]).

% find_name(+TargetVar, +List, -Name)
% We ignore 'word_all'
find_name(TargetVar, [var_pair(word_all, _) | Rest], Name) :-
    find_name(TargetVar, Rest, Name).

% Finds the name of a var from the prolog name
find_name(TargetVar, [var_pair(Name, Var) | _Rest], Name) :-
    Name \= word_all,
    TargetVar == Var.

% Recursive
find_name(TargetVar, [var_pair(_Name, Var) | Rest], Name) :-
    TargetVar \== Var,
    find_name(TargetVar, Rest, Name).

% Base case
find_name(TargetVar, [], TargetVar).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 5. TESTING
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% In this section, I tried to test my code in most of the possible cases.
% I also tried on two complex set of sentences, with the one given in the pdf too.
% To check my result, I tried the tests in the terminal and by hand on paper for the data.

:- begin_tests(assignment_5_tests).

    % Verification of new variable creation
    test(look_up_new_variable) :-
        look_up(v, [], [var_pair(word_all, false), var_pair(v, _)], _).

    % Verification of existing variable
    test(look_up_existing_variable) :-
        look_up(t, [], List, Variable1),
        look_up(t, List, _, Variable2),
        Variable1 == Variable2.

    % Distinction between different variables
    test(look_up_differents_vars) :-
        look_up(a, [], List1, Variable1),
        look_up(b, List1, _, Variable2),
        Variable1 \== Variable2.

    % Implicit creation of variables (with "The" it creates one implicitly)
    test(variable_creation_with_variable) :-
        Data = [
            'The', variable, q, equals, 100, fullstop
        ],
        lpsolve(Data, [var_pair(word_all, false), var_pair(q, 100)]).

    %  Reassignment of a value to a variable
    test(duplication_error) :-
        Data = [
            'A', variable, v, equals, 10, fullstop,
            'A', variable, v, equals, 20, fullstop
        ],
        \+ catch(lpsolve(Data, _), _, fail).

    % Math priority (2 + 5 * 3)
    % x = 17
    test(math_priority) :-
        Data = [
            'A', variable, x, equals, 2, +, 5, *, 3, fullstop
        ],
        lpsolve(Data, [var_pair(word_all, false), var_pair(x, 17)]).

    % Operator "+" synonyms (+/plus) (if it works for "+", it works for "-", "*", "/")
    % f = 10
    % g = 15
    % h = 15
    test(math_same_operators) :-
        Data = [
            'A', variable, f, equals, 10, fullstop,
            'A', variable, g, equals, f, plus, 5, fullstop,
            'A', variable, h, equals, f, +, 5, fullstop,
            variable, g, is, equal, to, h, fullstop
        ],
        lpsolve(Data, [var_pair(word_all, false), var_pair(f, 10), var_pair(h, 15), var_pair(g, 15)]).

    % Textual math operations
    % m = 6
    % n = 2
    % p = 12
    % q = 3
    test(math_textual_operations) :-
        Data = [
            'A', variable, m, equals, 6, fullstop,
            'A', variable, n, equals, 2, fullstop,
            'A', variable, o, equals, the, product, of, m, and, n, fullstop,
            'A', variable, p, equals, the, dividend, of, m, and, n, fullstop,
            variable, o, is, equal, to, 12, fullstop,
            variable, p, is, equal, to, 3, fullstop
        ],
        lpsolve(Data, [var_pair(word_all, false), var_pair(m, 6), var_pair(n, 2), var_pair(o, 12), var_pair(p, 3)]).

    % Small mix of calculatins
    % a = 3
    % b = 17
    test(math_small_mix) :-
        Data = [
            'A', variable, a, equals, 3, fullstop,
            'A', variable, b, equals, 5, plus, the, product, of, a, and, 4, fullstop
        ],
        lpsolve(Data, [var_pair(word_all, false), var_pair(a, 3), var_pair(b, 17)]).

    % Invalid mathematical operation
    test(math_logic_fail) :-
        \+ phrase(plus_and_minus(50, [], _), [10, +, 2]).

    % Differents "=" vocabulary
    % c = 10
    % d = 10
    test(grammar_assignment_synonyms) :-
        Data = [
            'A', variable, c, holds, 10, fullstop,
            'A', variable, d, contains, 10, fullstop,
            variable, c, equals, d, fullstop
        ],
        lpsolve(Data, [var_pair(word_all, false), var_pair(d, 10), var_pair(c, 10)]).

    % Can't use "It" at start
    test(it_with_no_var_before) :-
        \+ lpsolve([it, equals, 10, fullstop], _).

    % Error catch if use of "It" after "All"
    test(it_after_all_error) :-
        Data = [
            'The', variable, k, varies, from, 1, to, 5, fullstop,
            all, variables, are, greater, than, 0, fullstop,
            it, equals, 3, fullstop
        ],
        \+ catch(lpsolve(Data, _), _, fail).

    % All test
    % a = 50
    % b = 60
    test(all_range) :-
        Data = [
            'A', variable, a, equals, 50, fullstop,
            'A', variable, b, equals, 60, fullstop,
            all, variables, lies, between, 40, and, 70, fullstop
        ],
        lpsolve(Data, [var_pair(word_all, true), var_pair(a, 50), var_pair(b, 60)]).
        
    % Infinite Domain Test
    test(analyse_infinite_domain) :-
        Data = [
            'A', variable, k, is, greater, than, 500, fullstop
        ],
        call_residue_vars(lpsolve(Data, Variables), Res),
        analyse(Variables, Res).

    % Many sentences test
    % a in 3..20
    % b in 5..25
    % c in 10..30
    % c = a + b
    % b < 2 * a
    % a > b - 5
    % b >= c div 2
    test(full_data_test) :-
        Data = [
            'The', variable, a, varies, from, 0, to, 20, fullstop,
            variable, b, lies, between, 5, and, 25, fullstop,
            'A', variable, c, is, in, the, range, 10, to, 30, fullstop,
            it, equals, a, plus, b, fullstop,
            all, these, variables, are, greater, than, 2, fullstop,
            b, is, less, than, 2, *, a, fullstop,
            a, is, greater, than, b, minus, 5, fullstop,
            variable, b, is, greater, than, or, equal, to, the, quotient, of, c, and, 2, fullstop
        ],
        lpsolve(Data, Variables),
        member(var_pair(a, _), Variables),
        member(var_pair(b, _), Variables),
        member(var_pair(c, _), Variables).
        
    % Test given in pdf
    test(all_sentences_data) :-
        Data = [
            the, variable, x, lies, between, 0, and, 10, fullstop,
            variable, y, varies, from, 10, to, -10, fullstop,
            a, variable, z, is, in, the, range, 0, to, 15, fullstop,
            it, equals, x, plus, y, fullstop,
            all, these, variables, are, greater, than, -20, fullstop,
            y, is, less, than, 5, +, 2, *, x, fullstop,
            x, is, greater, than, y, times, 2, fullstop,
            variable, y, is, greater, than, or, equal, to, the, quotient, of, z, and, 4, fullstop
        ],
    lpsolve(Data, Variables),
    member(var_pair(x, _), Variables),
    member(var_pair(y, _), Variables),
    member(var_pair(z, _), Variables).

:- end_tests(assignment_5_tests).