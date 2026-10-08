import Submission.Blueprint.Interfaces

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ThompsonFrobenius`: bridge to the blueprint's vocabulary

Re-exports `Submission.Blueprint` (the `ZJ`, `pPrimeCore`, `oddCore`, area `Prop`s, ...) so that
the leaves of this area can be *delegated* with a `depends_on` entry (delegation paths must live
under `Submission/Work/`).  No declaration is copied or renamed here.
-/
