From elpi Require Import elpi.

Elpi Command attr.
Elpi Accumulate lp:{{

  main _ :-
    attributes A, % we fetch the list of attributes from the context
    coq.say {term_to_string A},
    coq.say A.

}}.

#[this, more(stuff="33")] Elpi attr.