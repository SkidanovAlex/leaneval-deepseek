/-
Area A3 (coprime action) of the Feit–Thompson drive: single entry point.

`import Submission.Work.Coprime.All` gives access to the whole area: the infrastructure
(`Defs`, `Basic`, `Internal`, `Normalizer`) and every main theorem.  See `NOTES.md` for the
description of the area and of each result.  The main theorems live in namespace `Work.Coprime`,
the infrastructure in namespace `FT`.
-/
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Basic
import Submission.Work.Coprime.Internal
import Submission.Work.Coprime.Normalizer

import Submission.Work.Coprime.commutator_normal
import Submission.Work.Coprime.complement_conj_prime_index
import Submission.Work.Coprime.cocycle_is_coboundary
import Submission.Work.Coprime.schurZassenhaus_conj_of_solvable_quotient
import Submission.Work.Coprime.fixedPoints_quotient
import Submission.Work.Coprime.commutator_fixedPoints_sup
import Submission.Work.Coprime.commutator_commutator_eq
import Submission.Work.Coprime.isTrivialOn_of_commutator_le_fixedPoints
import Submission.Work.Coprime.abelian_split
import Submission.Work.Coprime.isInvariant_map_subtype
import Submission.Work.Coprime.lt_inf_normalizer_of_lt
import Submission.Work.Coprime.exists_conj_le_of_isComplement
import Submission.Work.Coprime.conj_fixed_of_invariant
import Submission.Work.Coprime.glauberman_fixed_point_exists
import Submission.Work.Coprime.glauberman_exists_fixed
import Submission.Work.Coprime.glauberman_lemma
import Submission.Work.Coprime.exists_invariant_sylow_of_solvable
import Submission.Work.Coprime.exists_invariant_sylow
import Submission.Work.Coprime.exists_invariant_sylow_ge_of_solvable
import Submission.Work.Coprime.exists_invariant_sylow_ge
import Submission.Work.Coprime.invariant_sylow_conj
import Submission.Work.Coprime.trivial_of_trivial_on_frattiniQuotient
import Submission.Work.Coprime.trivial_of_trivial_on_omega1
import Submission.Work.Coprime.thompson_PxQ
import Submission.Work.Coprime.fixedPoints_ne_bot_of_isPGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end
