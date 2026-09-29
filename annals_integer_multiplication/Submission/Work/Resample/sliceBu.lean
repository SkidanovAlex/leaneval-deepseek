import Mathlib
import Submission.Work.Resample.buDefs
import Submission.Work.Resample.buApprox
import Submission.Work.Resample.buGaussTail
import Submission.Work.Resample.buPrep
import Submission.Work.Resample.buQW

/-!
# `Work.Resample.sliceBu` — the uniform one-dimensional `B̃` resampling word (paper Prop. 4.7(ii))

The computable weight table and the map `Φ = buPhi (buWt p α s t) (buWd p α s t)` are defined in
`Submission/Work/Resample/buDefs.lean`; the mathematical content (disc invariant and error bound)
in `Submission/Work/Resample/buApprox.lean`; the two uniform programs `prep` and `q` together with
their cost curves in `Work.Resample.buPrep` and `Work.Resample.buQW`.  This module assembles them
into the area interface (`Work.Resample.SliceSpecB`, hence `HvdH.ResampleProp`).
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

theorem sliceBu (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) (FL : HvdH.FxLib)
    (RM : HvdH.ResMath1DProp) :
    ∃ (prep q : HvdH.Cmd) (K : ℕ),
      ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) (htp : t < 2 ^ p)
        (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
        (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1),
      ∃ (Φ : (Fin t → ℤ × ℤ) → (Fin s → ℤ × ℤ)) (P : List HvdH.Val),
        (∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → K * p < N →
          HvdH.WordR main prep
            (fun vs => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest)
            (fun vs out => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest ∧
              out = P ++ rest)
            (fun _ => K * (t + 1) * (p + 1) ^ K)) ∧
        (∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → K * p < N →
          HvdH.WordR main q
            (fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val),
              vs = HvdH.ofList (u.map HvdH.cfxVal) :: P ++ rest ∧
              u.length = t ∧ (∀ z ∈ u, HvdH.inDisc p z))
            (fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val) (w : List (ℤ × ℤ)),
              vs = HvdH.ofList (u.map HvdH.cfxVal) :: P ++ rest ∧
              out = HvdH.cvecVal w :: P ++ rest ∧ w.length = s ∧ (∀ z ∈ w, HvdH.inDisc p z) ∧
              (∀ k : Fin s, w.getD k (0,0) = Φ (fun j => u.getD j (0,0)) k))
            (fun _ => K * (t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (K * p) + p + 1) +
              K * (t + 1) * (p + 1) ^ 2)) ∧
        (∀ w : Fin t → ℤ × ℤ, (∀ j, HvdH.inDisc p (w j)) → ∀ k : Fin s, HvdH.inDisc p (Φ w k)) ∧
        (∀ w : Fin t → ℤ × ℤ, (∀ j, HvdH.inDisc p (w j)) → ∀ k : Fin s,
          ‖HvdH.fxC p (Φ w k) - (HvdH.resB s t α).mulVec (fun j => HvdH.fxC p (w j)) k‖ * (2 : ℝ) ^ p
            < (p : ℝ) ^ 2) := by
  obtain ⟨prep, K₁, hprep⟩ := buPrep KL IL LL FL
  obtain ⟨q, K₂, hq⟩ := buQW KL IL LL FL
  exact buSliceGlue KL IL LL FL RM prep K₁ hprep q K₂ hq
    (fun p α s t hs hs0 hst hcop hα hp hαp hθ =>
      buPhiSpec RM p α s t hs hs0 hst hcop hα hp hαp hθ
        (fun ℓ => buGaussTail p α s t hs hst hα hp ℓ))

end Work.Resample
