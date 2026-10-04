import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.varLapStarDef
import Submission.Work.Diff.STE.B3.VarCoef.POp_sub_star_isOrd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.VarCoef

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-!
# The "swapped" difference `M_d ∘ D^k ∘ M_c - M_{c'} ∘ (D^*)^k ∘ M_{d'}`

`POp c c' D k = M_{c'} ∘ D^k ∘ M_c` and `POpStar c c' A B k = M_c ∘ (varLapStar A B)^k ∘ M_{c'}`.
The companion file `POp_sub_star_isOrd.lean` bounds the *adjoint pair*
`M_{c'} D^k M_c - M_c (D^*)^k M_{c'}`: there the two inner multipliers agree, which is exactly the
adjoint structure.

Here the two inner multipliers are *different* (`c` inside the first term, `d'` inside the second),
and the coupling hypothesis is the pointwise identity `d z * c z = c' z * d' z`, i.e. the two
"coefficient products" `M_d M_c` and `M_{c'} M_{d'}` agree.  The proof splits

`M_d D^k M_c - M_{c'} (D^*)^k M_{d'} = (M_d D^k M_c - M_c (D^*)^k M_d)
                                     - (M_c [M_d,(D^*)^k] - M_{c'} [M_{d'},(D^*)^k])`

(the first bracket is the adjoint pair of `POp_sub_star_isOrd`, the second is a sum of commutators —
hence of order `2k - 1`), which uses the cancellation
`M_c E^k M_d + M_c [M_d,E^k] = M_c M_d E^k = M_{c'} M_{d'} E^k = M_{c'} E^k M_{d'} +
M_{c'}[M_{d'},E^k]` with `E := varLapStar A B`.  Both pieces therefore have order `2k - 1`.
-/

/-- `[T, A - B] = [T,A] - [T,B]` when `T` is additive on smooth periodic functions. -/
theorem commOp_sub_right_apply {T A B : Op ι} {f : (ι → ℝ) → ℂ} (hT : LinSP T)
    (hA : Preserves A) (hB : Preserves B) (hf : SmoothPer f) :
    commOp T (A - B) f = commOp T A f - commOp T B f := by
  have h2 : SmoothPer (A f) := hA f hf
  have h3 : SmoothPer (B f) := hB f hf
  funext x
  simp only [commOp_apply, Pi.sub_apply]
  rw [linSP_map_sub hT h2 h3]
  simp only [Pi.sub_apply]
  ring

/-- `commOp T ·` depends only on the values of its second argument on smooth periodic functions. -/
theorem commOp_congr {T A B : Op ι} (hT : Preserves T)
    (h : ∀ f, SmoothPer f → A f = B f) {f : (ι → ℝ) → ℂ} (hf : SmoothPer f) :
    commOp T A f = commOp T B f := by
  simp only [commOp_apply]
  rw [h f hf, h (T f) (hT f hf)]

/-- **`POp c d (varLap A B) k - POpStar c' d' A B k` has order `2k - 1`.**  This is the "swapped"
form of `POp_sub_star_isOrd`: the inner multipliers `c` and `d'` differ, but the products
`d · c` and `c' · d'` agree pointwise, so the two principal symbols still cancel. -/
theorem POp_swap_sub_star_isOrd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : 1 ≤ k)
    {A : ι → ι → (ι → ℝ) → ℝ} {B : ι → (ι → ℝ) → ℝ} {c d c' d' : (ι → ℝ) → ℝ}
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Work.Diff.STE.Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Work.Diff.STE.Periodic1 (B a))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcp : Work.Diff.STE.Periodic1 c)
    (hd : ContDiff ℝ (⊤ : ℕ∞) d) (hdp : Work.Diff.STE.Periodic1 d)
    (hc' : ContDiff ℝ (⊤ : ℕ∞) c') (hc'p : Work.Diff.STE.Periodic1 c')
    (hd' : ContDiff ℝ (⊤ : ℕ∞) d') (hd'p : Work.Diff.STE.Periodic1 d')
    (hprod : ∀ z, d z * c z = c' z * d' z) :
    ∃ C : ℤ → ℝ, Work.Diff.STE.B3.VarCoef.IsOrd (2 * (k : ℤ) - 1) C
      (Work.Diff.STE.B3.VarCoef.POp c d (Work.Diff.STE.B3.VarCoef.varLapOp A B) k
        - Work.Diff.STE.B3.VarCoef.POpStar c' d' A B k) := by
  classical
  -- order-`0` certificates for the multipliers
  obtain ⟨Cc, hCc⟩ := mulOp_isOrd c hc hcp
  obtain ⟨Cc', hCc'⟩ := mulOp_isOrd c' hc' hc'p
  -- the `varLap` certificates against `M_d` and `M_{d'}`
  obtain ⟨_, _, hVLd⟩ := varLapOp_isCommOrd_mulOp d hd hdp A B hA hAp hB hBp
  obtain ⟨_, _, hVLd'⟩ := varLapOp_isCommOrd_mulOp d' hd' hd'p A B hA hAp hB hBp
  -- the Leibniz difference `varLap - varLapStar` has order `1`
  obtain ⟨CDE, hDE⟩ := varLap_sub_varLapStar_isOrd_local A B hA hAp hB hBp
  have hDE2 : IsOrd 2 CDE (varLapOp A B - varLapStarOp A B) :=
    IsOrd.mono_d hDE (by norm_num)
  -- `varLapStar` has order `2`
  obtain ⟨CE, hEord⟩ : ∃ C : ℤ → ℝ, IsOrd 2 C (varLapStarOp A B) :=
    ⟨_, IsOrd.congr (T := varLapOp A B - (varLapOp A B - varLapStarOp A B))
      (IsOrd.sub hVLd.ord hDE2) (fun f _ => by
        funext x
        simp only [Pi.sub_apply, varLapStarOp]
        abel)⟩
  -- `[M_m, varLapStar]` has order `1`
  have hEcomm : ∀ (m : (ι → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) m → Work.Diff.STE.Periodic1 m →
      ∃ C : ℤ → ℝ, IsOrd 1 C (commOp (mulOp m) (varLapStarOp A B)) := by
    intro m hm hmp
    obtain ⟨Cm, hCm⟩ := mulOp_isOrd m hm hmp
    obtain ⟨_, _, hVLm⟩ := varLapOp_isCommOrd_mulOp m hm hmp A B hA hAp hB hBp
    obtain ⟨C2, hc2⟩ : ∃ C : ℤ → ℝ,
        IsOrd 1 C (commOp (mulOp m) (varLapOp A B - varLapStarOp A B)) :=
      ⟨_, IsOrd.comm hCm hDE⟩
    refine ⟨_, IsOrd.congr
      (T := commOp (mulOp m) (varLapOp A B)
        - commOp (mulOp m) (varLapOp A B - varLapStarOp A B))
      (IsOrd.sub hVLm.comm hc2) ?_⟩
    intro f hf
    have hAB : ∀ g : (ι → ℝ) → ℂ, SmoothPer g →
        varLapStarOp A B g = (varLapOp A B - (varLapOp A B - varLapStarOp A B)) g := by
      intro g _
      funext x
      simp only [Pi.sub_apply, varLapStarOp]
      abel
    rw [commOp_congr (T := mulOp m) hCm.pres hAB hf]
    exact (commOp_sub_right_apply (T := mulOp m) hCm.lin hVLm.ord.pres hDE.pres hf).symm
  -- `[M_m, (varLapStar)^k]` has order `2k - 1`
  have hcommk : ∀ (m : (ι → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) m → Work.Diff.STE.Periodic1 m →
      ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
        (commOp (mulOp m) ((varLapStarOp A B)^[k])) := by
    intro m hm hmp
    obtain ⟨CEm, hEm⟩ := hEcomm m hm hmp
    obtain ⟨Ck, hk'⟩ := isOrd_commOp_iterate hEord hEm (linSP_mulOp m) (pres_mulOp m hm hmp) k
    exact ⟨Ck, IsOrd.mono_d (d := 2 * (k : ℤ) - 1) (d' := 1 + 2 * (k : ℤ) - 2) hk'
      (by omega)⟩
  obtain ⟨E1, hE1⟩ := hcommk d hd hdp
  obtain ⟨E2, hE2⟩ := hcommk d' hd' hd'p
  -- the two terms of the second bracket, composed with `M_c` and `M_{c'}`
  obtain ⟨C1, hC1⟩ : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (compOp (mulOp c) (commOp (mulOp d) ((varLapStarOp A B)^[k]))) :=
    ⟨_, IsOrd.mono_d (d := 2 * (k : ℤ) - 1) (d' := 0 + (2 * (k : ℤ) - 1))
      (IsOrd.comp (T := mulOp c) (U := commOp (mulOp d) ((varLapStarOp A B)^[k])) hCc hE1)
      (by omega)⟩
  obtain ⟨C2, hC2⟩ : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (compOp (mulOp c') (commOp (mulOp d') ((varLapStarOp A B)^[k]))) :=
    ⟨_, IsOrd.mono_d (d := 2 * (k : ℤ) - 1) (d' := 0 + (2 * (k : ℤ) - 1))
      (IsOrd.comp (T := mulOp c') (U := commOp (mulOp d') ((varLapStarOp A B)^[k])) hCc' hE2)
      (by omega)⟩
  have hsecond : IsOrd (2 * (k : ℤ) - 1) (fun t => 2 * (C1 t + C2 t))
      (compOp (mulOp c) (commOp (mulOp d) ((varLapStarOp A B)^[k]))
        - compOp (mulOp c') (commOp (mulOp d') ((varLapStarOp A B)^[k]))) :=
    IsOrd.sub hC1 hC2
  -- the adjoint pair, with inner multipliers `c` and `d` (i.e. `c' := d` in the companion lemma)
  obtain ⟨Cf, hfirst⟩ := POp_sub_star_isOrd (A := A) (B := B) (c := c) (c' := d)
    k hk hA hAp hB hBp hc hcp hd hdp
  refine ⟨_, IsOrd.congr
    (T := (POp c d (varLapOp A B) k - POpStar c d A B k)
      - (compOp (mulOp c) (commOp (mulOp d) ((varLapStarOp A B)^[k]))
        - compOp (mulOp c') (commOp (mulOp d') ((varLapStarOp A B)^[k]))))
    (IsOrd.sub hfirst hsecond) ?_⟩
  intro f hf
  funext x
  simp only [Pi.sub_apply, POp, POpStar, compOp_apply, commOp_apply, mulOp]
  have hcdC : ((d x : ℝ) : ℂ) * ((c x : ℝ) : ℂ) = ((c' x : ℝ) : ℂ) * ((d' x : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hprod x]
  ring_nf
  rw [hcdC]
  ring

end Work.Diff.STE.B3.VarCoef
