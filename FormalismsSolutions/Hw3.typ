= Ex 2.5

*Definition* (_fairness_): By fairness we mean that when performing a choice of the clauses and the atom of their intersection, we will eventually (after a finite amount of steps) pick any possible combination. The idea is similar to how we want thread scheduling to be fair, meaning every thread eventually gets to run.

We define #smallcaps[FairBooleanResolution] in the following way. Assume that we have some total order on the countably infinite clauses in $C = {gamma_1, gamma_2, ...}$.

+ foreach $n$ in ${1, 2, ...}$
  + let $C' := {gamma_i | i <= n}$
  + if $bot in C'$ then return #smallcaps[Yes]
  + let $"added" := "true"$
  + while $"added"$
    + $"added" := "false"$
    + let $C'' := C'$
    + foreach $c_1$ in $C''$
      + foreach $c_2$ in $C''$
        + foreach $p$ in $c_1^+ inter c_2^-$
          + let $c = ((c_1^+ union c_2^+) - p, (c_1^- union c_2^-) - p)$
          + if $c = bot$ then return #smallcaps[Yes]
          + if $c in.not C'$ then $C' := C' + c$ and $"added" := "true"$

*Theorem* 1: #smallcaps[FairBooleanResolution] is fair.

*Proof*: We iterate over all pairs of $c_1, c_2 in C''$ eventually reaching every combination. $c_1^+ inter c_2^-$ is a finite set, we can iterate over it in any order eventually picking every $p$. Every time $C'$ is mutated, we go over all elements again. We iterate over all prefixes of $C$, eventually reaching all of them.


*Theorem* 2: When $C$ is unsat, #smallcaps[FairBooleanResolution] terminates with #smallcaps[Yes].

*Proof*: The algorithm follows the same strategy as #smallcaps[PropositionalResolution] which was proven in lecture notes to find unsat. We only replace non-determinism with fair choices. Only the top loop is unbounded, but if $C$ is unsat, we will eventually reach the $C$-prefix leading to a $bot$. By compactness we know that if $C$ is unsat, we will be able to derive $bot$ from a finite


#smallcaps[FairBooleanResolution] never returns #smallcaps[No]. Instead, it always diverges on a sat set of infinite clauses $C$.

= Ex. 2.7

Consider $phi_n = (a_1 and b_1) or ... or (a_n and b_n)$.

#let le1 = $scripts(<)_1$
#let le2 = $scripts(<)_2$

We define $le1$ to be
$ a_1 le1 a_2 le1 ... le1 a_n le1 b_1 le1 b_2 le1 ... le1 b_n $

, and $le2$ to be
$ a_1 le2 b_1 le2 a_2 le2 b_2 le2 ... le2 a_n le2 b_n $.

We define $|phi_n|$ as the number of conjunctive clauses, thus $|phi_n| = n$.

*Theorem* 1: The $le1$-ordered BDD for $phi_n$ is of size $Omega(2^(|phi_n|))$

*Proof*: By induction on $n$

1. For $n = 1$, the BDD has size $2 = Omega(2^1) = Omega(2^(|phi_1|))$
2. For $n + 1$, suppose that in the BDD for $phi_n$ has size $Omega(2^(|phi_n|))$

  Now consider $phi_(n+1) = phi_n or (a_(n+1) and b_(n+1))$. Because the $b$-variables all come after $a_(n+1)$ in $le1$, by the time we reach $a_(n+1)$ we still haven't seen any $b_i$. Therefore none of the first $n$ clauses have been resolved yet. Thus, the top $n$ levels behave just as in $phi_n$, reaching $2^n$ distinct $a_(n+1)$-nodes.

  At each of these $2^n$ nodes for $a_(n+1)$, setting $a_(n+1) = top$ makes the new clause $(a_(n+1) and b_(n+1))$ depend on $b_(n+1)$, whereas setting $a_(n+1) = bot$ drops it. Since each of the $2^n$ branches already remembers a unique subset of active $b_1, dots, b_n$ variables, adding or not adding $b_(n+1)$ produces $2 dot 2^n = 2^(n+1)$ distinct combinations that must be kept separate entering the $b$-levels.

*Theorem* 2: The $le2$-ordered BDD for $phi_n$ is of size $cal(O)(|phi_n|)$

*Proof*: In that BDD,

1. $a_i$ nodes point to
  - $b_i$ for iftrue: the conjunctive clause $a_i and b_i$ is turned into $top and b_i$ which is equivalent to just $b_i$
  - $a_(i+1)$ for iffalse when $i eq.not n$: the conjunctive clause $a_i and b_i$ is turned into $bot and b_i$ which is equivalent to just $bot$
  - $bot$ for iffalse when $i = n$: the conjunctive clause $a_i and b_i$ is turned into $bot and b_i$ which is equivalent to just $bot$ (but we are out of conjuctive clauses)
2. $b_i$ nodes point to
  - $top$ for iftrue: the conjunctive clause is only $b_i$ at this point, which is turned into $top$
  - $a_(i+1)$ for iffalse when $i eq.not n$: the conjunctive clause is only $b_i$ at this point, which is turned into $bot$
  - $bot$ for iffalse when $i = n$: the conjunctive clause is only $b_i$ at this point, which is turned into $bot$ (but we are out of conjuctive clauses)

So we have only a single BDD node per $a_i$, $b_i$ and thus the size of the BDD is $cal(O)(|phi_n|)$.

*Theorem* 3: The sizes of the $le1$-ordered BDD for $phi_n$ and the $le2$-ordered BDD for $phi_n$ differ by $Omega(2^(|phi_n|))$

*Proof*: By theorem 1 and 2, $Omega(2^(|phi_n|)) - cal(O)(|phi_n|) = Omega(2^(|phi_n|))$.
