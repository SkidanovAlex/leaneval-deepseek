/-
  WilG0 — the Ω-formula calculus (the deliverable `G0_calculus`).

  We prove a slightly stronger, explicit-format form: the format bound is a *function*
  `oFmt F s` of the shape and of `F` alone, while the degree is exactly the shape degree
  `s.deg d` (degrees add, `+2` per substitution atom).  The frozen existential statement
  `WilkiesDesign.CG.G0_calculus_proved` is the immediate corollary, with `a := oFmt F s`.

  The induction over `OShape` mirrors the axioms of `SOMin`:
  * `poly`   — `SOMin.hyp` (format `n`, degree `P.totalDegree`);
  * `mem`    — `substSet_mem` (`+2` degree, format from a lift, a diagonal and `m` projections);
  * `neg`    — `SOMin.compl`  (format `+1`);
  * `and`    — `Omega_inter2` (format `+1`, degrees add);
  * `or`     — `Omega_union2` (format unchanged, degrees add);
  * `ex`     — `SOMin.proj`   (format `+1`).
-/
import Submission.Work.WilG0.API
import Submission.Work.WilG0.Fmt
import Submission.Work.WilG0.Subst
import Submission.Work.WilG0.Good_mono_F

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG0

open WilkiesDesign
open WilkiesDesign.CG

/-- **G0, explicit form:** a good shape is realised in the format `oFmt F s` and the exact
shape degree `s.deg d`. -/
theorem realize_mem_Omega (S : SOMin) {n : ℕ} (s : OShape n) :
    ∀ (F : ℕ) (d : s.Data), s.Good S F d →
      s.realize d ∈ S.Ω (oFmt F s) (s.deg d) n := by
  induction s with
  | poly n => intro F d _; exact S.hyp n d
  | mem n m ι => intro F d hd; exact substSet_mem hd n ι
  | neg s ih => intro F d hd; exact S.compl (ih F d hd)
  | and s t ihs iht =>
    intro F d hd
    obtain ⟨hd1, hd2⟩ := hd
    have h1 := Omega_mono_F (le_max_left (oFmt F s) (oFmt F t)) (ihs F d.1 hd1)
    have h2 := Omega_mono_F (le_max_right (oFmt F s) (oFmt F t)) (iht F d.2 hd2)
    exact Omega_inter2 h1 h2
  | or s t ihs iht =>
    intro F d hd
    obtain ⟨hd1, hd2⟩ := hd
    have h1 := Omega_mono_F (le_max_left (oFmt F s) (oFmt F t)) (ihs F d.1 hd1)
    have h2 := Omega_mono_F (le_max_right (oFmt F s) (oFmt F t)) (iht F d.2 hd2)
    exact Omega_union2 h1 h2
  | ex s ih => intro F d hd; exact S.proj (ih F d hd)

/-- **G0 (the area hole), proved.** -/
theorem G0_calculus_proved (S : SOMin) {n : ℕ} (s : OShape n) (F : ℕ) :
    ∃ a : ℕ, ∀ d : s.Data, s.Good S F d → s.realize d ∈ S.Ω a (s.deg d) n :=
  ⟨oFmt F s, fun d hd => realize_mem_Omega S s F d hd⟩

/-- Convenience form: if the atoms merely lie in *some* format `F ≤ F'`, the realisation still
lies in the shape format computed from `F'`, in the exact shape degree. -/
theorem realize_mem_Omega_mono (S : SOMin) {n : ℕ} (s : OShape n) {F F' : ℕ} (h : F ≤ F')
    (d : s.Data) (hd : s.Good S F d) : s.realize d ∈ S.Ω (oFmt F' s) (s.deg d) n :=
  realize_mem_Omega S s F' d (Good_mono_F s h hd)

end Work.WilG0

namespace WilkiesDesign.CG

open WilkiesDesign

/-- **G0**, the area hole of `Submission/Work/Wilkies/CG/Spec.lean`, proved.  The statement is
copied verbatim from the spec; the proof is `Work.WilG0.G0_calculus_proved`. -/
theorem G0_calculus_proved (S : SOMin) {n : ℕ} (s : OShape n) (F : ℕ) :
    ∃ a : ℕ, ∀ d : s.Data, s.Good S F d → s.realize d ∈ S.Ω a (s.deg d) n :=
  Work.WilG0.G0_calculus_proved S s F

end WilkiesDesign.CG
