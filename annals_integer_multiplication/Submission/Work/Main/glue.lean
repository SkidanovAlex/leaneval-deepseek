import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Main.defs

/-!
# Glue lemmas for assembling the main step: chaining `WordR` triples with constant costs.
-/

set_option autoImplicit false

namespace Work.Main

open HvdH

/-- Chain two words with constant costs. The post is the accumulated existential. -/
theorem chain2c (hKer : KernelLib) {main p q : Cmd}
    {P : List Val → Prop} {Q : List Val → List Val → Prop} {c₁ : ℕ}
    {P' : List Val → Prop} {Q' : List Val → List Val → Prop} {c₂ : ℕ}
    (h1 : WordR main p P Q (fun _ => c₁)) (h2 : WordR main q P' Q' (fun _ => c₂))
    (h : ∀ vs mid, P vs → Q vs mid → P' mid) :
    WordR main (.seq p q) P (fun vs out => ∃ mid, Q vs mid ∧ Q' mid out) (fun _ => c₁ + c₂) := by
  refine hKer.seq main p q P Q (fun _ => c₁) P' Q' (fun _ => c₂) (fun _ => c₂) h1 h2 ?_
  intro vs mid hp hq
  exact ⟨h vs mid hp hq, le_rfl⟩

/-- `conseq` with named arguments. -/
theorem conseq' (hKer : KernelLib) {main p : Cmd}
    {P P' : List Val → Prop} {Q Q' : List Val → List Val → Prop} {C C' : List Val → ℕ}
    (h : WordR main p P Q C) (hP : ∀ vs, P' vs → P vs)
    (hQ : ∀ vs out, P' vs → Q vs out → Q' vs out) (hC : ∀ vs, P' vs → C vs ≤ C' vs) :
    WordR main p P' Q' C' := hKer.conseq main p P P' Q Q' C C' h hP hQ hC

end Work.Main
