/-
  WilE10 — `E10_subpf_to_rexp`: the frozen statement, from the core construction.
-/
import Submission.Work.WilE10.SubPfRexp.subpf_to_rexp_core

set_option autoImplicit false
noncomputable section
open Classical

namespace WilkiesDesign.E

open WilkiesDesign

/-- **E10b.** The `psiV`-preimage of a sub-Pfaffian set is `rexp`-existential. -/
theorem E10_subpf_to_rexp_proved {n : ℕ} (Z : Set (Fin n → ℝ)) (h : SubPf n Z) :
    RExpExist (psiV ⁻¹' Z) :=
  Work.WilE10.SubPfRexp.subpf_to_rexp_core n Z h

end WilkiesDesign.E
