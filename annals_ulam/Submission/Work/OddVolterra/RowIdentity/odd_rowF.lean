import Submission.Work.OddVolterra.RowIdentity.Basic
import Submission.Work.OddVolterra.RowIdentity.momentF_eq_AA_add_WW
import Submission.Work.OddVolterra.RowIdentity.kvec_zero_div_sqrt_eq
import Submission.Work.OddVolterra.RowIdentity.yend_iteratedDeriv_eq_rpow
import Submission.Work.OddVolterra.window_iteratedDeriv_smooth
import Submission.Work.Analysis.Calculus.contDiff_dslope
import Submission.Work.Analysis.Abel.swept_iteratedDeriv_rpow
import Submission.Work.OddVolterra.RowIdentity.Qy_Qx_rect_pos
import Submission.Work.OddVolterra.RowIdentity.contDiffAt_AA
import Submission.Work.OddVolterra.RowIdentity.contDiffAt_WW
import Submission.Work.OddVolterra.RowIdentity.section_box
import Submission.Work.OddVolterra.RowIdentity.WWDefs

namespace Work.OddVolterra.RowIdentity

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Commons.Geometry.Ulam (profileX semicircle)

noncomputable section

section Ident

variable (H : Setup)

/-- `hquot` is the divided difference `dslope`; in particular it is smooth in its first
variable. -/
lemma hquot_eq_dslope (u σ : ℝ) : hquot H.h u σ = dslope H.h u σ := by
  rcases eq_or_ne u σ with rfl | hne
  · rw [hquot_self, dslope_same]
  · rw [dslope_of_ne _ hne.symm]
    unfold slope
    simp only [smul_eq_mul, vsub_eq_sub]
    rw [eq_inv_mul_iff_mul_eq₀ (sub_ne_zero.mpr hne.symm)]
    exact (sub_mul_hquot (H.hh.of_le (by norm_num)) u σ).symm

lemma contDiff_dslope_fix (σ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => dslope H.h u σ) :=
  (Work.Analysis.Calculus.contDiff_dslope H.h H.hh).comp (contDiff_id.prodMk contDiff_const)

lemma contDiff_hquot_fst (σ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => hquot H.h u σ) := by
  have h := contDiff_dslope_fix H σ
  have he : (fun u : ℝ => hquot H.h u σ) = (fun u : ℝ => dslope H.h u σ) :=
    funext (fun u => hquot_eq_dslope H u σ)
  rwa [he]

lemma contDiff_Qy (σ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => Qy H.h H.y u σ) := by
  have hd := contDiff_hquot_fst H σ
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => line H.h σ (H.y σ) + line H.h u (H.y σ)) := by
    unfold line
    exact contDiff_const.add ((contDiff_id.mul contDiff_const).add H.hh)
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => H.y σ + hquot H.h u σ) :=
    contDiff_const.add hd
  unfold Qy
  exact h1.mul h2

lemma contDiff_Qx (σ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => Qx H.h H.x u σ) := by
  have hd := contDiff_hquot_fst H σ
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => line H.h σ (-(H.x σ)) + line H.h u (-(H.x σ))) := by
    unfold line
    exact contDiff_const.add ((contDiff_id.mul contDiff_const).add H.hh)
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => -(H.x σ) + hquot H.h u σ) :=
    contDiff_const.add hd
  unfold Qx
  exact h1.mul h2

/-- `E1` written with the globally smooth radicand `Psi`. -/
lemma E1_eq (s : ℝ) :
    E1 H.n H.h s = ∫ t in (-(profileX 1))..(profileX 1),
      iteratedDeriv (H.n + 1) (fun u : ℝ => (Psi H.h u t) ^ H.n * Real.sqrt (Psi H.h u t)) s := by
  unfold E1
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [uIcc_of_le (by linarith [profileX_one_pos] : -(profileX 1) ≤ profileX 1)] at ht
  have hmem : t ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by linarith [profileX_one_le_one, ht.1], by linarith [profileX_one_le_one, ht.2]⟩
  refine congrArg (fun g : ℝ → ℝ => iteratedDeriv (H.n + 1) g s) ?_
  funext u
  rw [Psi_eq_psi_semicircle H.h hmem]

/-- The fixed part of the section integral has `(n+1)`-st derivative equal to `E1`. -/
lemma iteratedDeriv_AA (s : ℝ) (hs : s ∈ Set.Icc H.a H.c) :
    iteratedDeriv (H.n + 1) (AA H.n H.h) s = E1 H.n H.h s := by
  rw [E1_eq H s]
  obtain ⟨ε, hε, hε'⟩ := Setup.Psi_window_pos H hs
  have hΨ : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => Psi H.h q.1 q.2) := by
    unfold Psi
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => q.1 * q.2 + H.h q.1) :=
      (contDiff_fst.mul contDiff_snd).add (H.hh.comp contDiff_fst)
    exact (contDiff_const.sub (contDiff_snd.pow 2)).sub (h2.pow 2)
  have h := window_iteratedDeriv_smooth H.n H.hn
    (show (-(profileX 1) : ℝ) ≤ profileX 1 by linarith [profileX_one_pos]) hΨ ⟨ε, hε, hε'⟩
  rw [show iteratedDeriv (H.n + 1) (AA H.n H.h) s
      = iteratedDeriv (H.n + 1) (fun u : ℝ => ∫ t in (-(profileX 1))..(profileX 1),
          Psi H.h u t ^ H.n * Real.sqrt (Psi H.h u t)) s from rfl]
  exact h

/-- The two endpoint factors of the frozen radicand, in explicit form. -/
def Ey (h y : ℝ → ℝ) (u σ : ℝ) : ℝ :=
  (y σ + hquot h u σ) * (line h σ (y σ) + line h u (y σ))

def Ex (h x : ℝ → ℝ) (u σ : ℝ) : ℝ :=
  (-(x σ) + hquot h u σ) * (line h σ (-(x σ)) + line h u (-(x σ)))

lemma contDiff_Ey (σ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => Ey H.h H.y u σ) := by
  rw [show (fun u : ℝ => Ey H.h H.y u σ) = (fun u : ℝ => Qy H.h H.y u σ) from rfl]
  exact contDiff_Qy H σ

lemma contDiff_Ex (σ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => Ex H.h H.x u σ) := by
  rw [show (fun u : ℝ => Ex H.h H.x u σ) = (fun u : ℝ => Qx H.h H.x u σ) from rfl]
  exact contDiff_Qx H σ

/-- The `√(σ-s)`-normalized kernel at `(s,σ)` is the `(n+1)`-st `u`-derivative at `u = s` of the
swept integrand, in explicit form. -/
lemma kvec_ident (s σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hsσ : s < σ)
    (hQy : ∃ ε > 0, ∀ u : ℝ, |u - s| < ε → 0 < Ey H.h H.y u σ)
    (hQx : ∃ ε > 0, ∀ u : ℝ, |u - s| < ε → 0 < Ex H.h H.x u σ)
    (hQyσ : 0 < Ey H.h H.y s σ) (hQxσ : 0 < Ex H.h H.x s σ) :
    (Kvec H.n H.h s σ (H.x σ) (H.y σ) (deriv H.x σ) (deriv H.y σ)) 0 / Real.sqrt (σ - s)
      = iteratedDeriv (H.n + 1)
          (fun u : ℝ => (σ - u) ^ ((H.n : ℝ) + 1 / 2) *
            ((Ey H.h H.y u σ) ^ ((H.n : ℝ) + 1 / 2) * (-(deriv H.y σ))
             + (Ex H.h H.x u σ) ^ ((H.n : ℝ) + 1 / 2) * (-(deriv H.x σ)))) s := by
  have hh1 : ContDiff ℝ 1 H.h := H.hh.of_le (by norm_num)
  have hσmem : σ ∈ Set.Ioc (0 : ℝ) 1 := ⟨hσ0, hσ1⟩
  have henvy := (H.hxy σ hσmem).1
  have henvx := (H.hxy σ hσmem).2
  -- the `-x`-endpoint version is the `y`-endpoint version for the reflected data
  have hxinst := yend_iteratedDeriv_eq_rpow (h := H.h) (f := fun t => -(H.f t))
    (y := fun u => -(H.x u)) H.n hh1 hsσ
    (show (fun t => -(H.f t)) (-(H.x σ)) = σ * (-(H.x σ)) + H.h σ by
      linarith [henvx])
    (by
      obtain ⟨ε, hε, hε'⟩ := hQx
      exact ⟨ε, hε, fun u hu => by simpa only [Ex] using hε' u hu⟩)
  have hxcnv : (fun u : ℝ => psi H.h H.f u (-(H.x σ)) ^ H.n *
        Real.sqrt (psi H.h H.f u (-(H.x σ))))
      = fun u : ℝ => psi H.h (fun t => -H.f t) u (-(H.x σ)) ^ H.n *
          Real.sqrt (psi H.h (fun t => -H.f t) u (-(H.x σ))) := by
    funext u
    simp only [psi, neg_sq]
  rw [kvec_zero_div_sqrt_eq H.n hh1 hsσ henvy henvx
    (by simpa only [Ey] using hQyσ) (by simpa only [Ex] using hQxσ)]
  rw [yend_iteratedDeriv_eq_rpow H.n hh1 hsσ henvy (by simpa only [Ey] using hQy)]
  rw [hxcnv, hxinst]
  -- fold the two endpoint factors back into `Ey`, `Ex`
  have fold_y : (fun u : ℝ => (σ - u) ^ ((H.n : ℝ) + 1 / 2) *
        ((H.y σ + hquot H.h u σ) * (line H.h σ (H.y σ) + line H.h u (H.y σ))) ^
          ((H.n : ℝ) + 1 / 2))
      = fun u : ℝ => (σ - u) ^ ((H.n : ℝ) + 1 / 2) * (Ey H.h H.y u σ) ^ ((H.n : ℝ) + 1 / 2) :=
    rfl
  have fold_x : (fun u : ℝ => (σ - u) ^ ((H.n : ℝ) + 1 / 2) *
        ((-(H.x σ) + hquot H.h u σ) * (line H.h σ (-(H.x σ)) + line H.h u (-(H.x σ)))) ^
          ((H.n : ℝ) + 1 / 2))
      = fun u : ℝ => (σ - u) ^ ((H.n : ℝ) + 1 / 2) * (Ex H.h H.x u σ) ^ ((H.n : ℝ) + 1 / 2) :=
    rfl
  rw [fold_y, fold_x]
  -- smoothness of the two endpoint factors
  have hEy : ContDiffAt ℝ (↑(H.n + 1)) (fun u : ℝ => Ey H.h H.y u σ) s :=
    ((contDiff_Ey H σ).contDiffAt).of_le
      (WithTop.coe_le_coe.mpr (le_top : ((H.n : ℕ∞) + 1) ≤ (⊤ : ℕ∞)))
  have hEx : ContDiffAt ℝ (↑(H.n + 1)) (fun u : ℝ => Ex H.h H.x u σ) s :=
    ((contDiff_Ex H σ).contDiffAt).of_le
      (WithTop.coe_le_coe.mpr (le_top : ((H.n : ℕ∞) + 1) ≤ (⊤ : ℕ∞)))
  have hsu : ContDiffAt ℝ (↑(H.n + 1)) (fun u : ℝ => σ - u) s :=
    (contDiff_const.sub contDiff_id).contDiffAt
  have hp : ContDiffAt ℝ (↑(H.n + 1)) (fun u : ℝ => (σ - u) ^ ((H.n : ℝ) + 1 / 2)) s :=
    hsu.rpow contDiffAt_const (by simpa using (sub_ne_zero.mpr (ne_of_gt hsσ)))
  have hey : ContDiffAt ℝ (↑(H.n + 1))
      (fun u : ℝ => (Ey H.h H.y u σ) ^ ((H.n : ℝ) + 1 / 2)) s :=
    hEy.rpow contDiffAt_const (by simpa using (ne_of_gt hQyσ))
  have hex : ContDiffAt ℝ (↑(H.n + 1))
      (fun u : ℝ => (Ex H.h H.x u σ) ^ ((H.n : ℝ) + 1 / 2)) s :=
    hEx.rpow contDiffAt_const (by simpa using (ne_of_gt hQxσ))
  have hFy : ContDiffAt ℝ (↑(H.n + 1))
      (fun u : ℝ => (σ - u) ^ ((H.n : ℝ) + 1 / 2) * (Ey H.h H.y u σ) ^ ((H.n : ℝ) + 1 / 2)) s :=
    hp.mul hey
  have hFx : ContDiffAt ℝ (↑(H.n + 1))
      (fun u : ℝ => (σ - u) ^ ((H.n : ℝ) + 1 / 2) * (Ex H.h H.x u σ) ^ ((H.n : ℝ) + 1 / 2)) s :=
    hp.mul hex
  have hsplit : (fun u : ℝ => (σ - u) ^ ((H.n : ℝ) + 1 / 2) *
        ((Ey H.h H.y u σ) ^ ((H.n : ℝ) + 1 / 2) * (-(deriv H.y σ))
         + (Ex H.h H.x u σ) ^ ((H.n : ℝ) + 1 / 2) * (-(deriv H.x σ))))
      = (fun u : ℝ => (-(deriv H.y σ)) *
            ((σ - u) ^ ((H.n : ℝ) + 1 / 2) * (Ey H.h H.y u σ) ^ ((H.n : ℝ) + 1 / 2)))
        + fun u : ℝ => (-(deriv H.x σ)) *
            ((σ - u) ^ ((H.n : ℝ) + 1 / 2) * (Ex H.h H.x u σ) ^ ((H.n : ℝ) + 1 / 2)) := by
    funext u
    simp only [Pi.add_apply]
    ring
  have hA : ContDiffAt ℝ (↑(H.n + 1))
      (fun u : ℝ => (-(deriv H.y σ)) *
        ((σ - u) ^ ((H.n : ℝ) + 1 / 2) * (Ey H.h H.y u σ) ^ ((H.n : ℝ) + 1 / 2))) s :=
    contDiffAt_const.mul hFy
  have hB : ContDiffAt ℝ (↑(H.n + 1))
      (fun u : ℝ => (-(deriv H.x σ)) *
        ((σ - u) ^ ((H.n : ℝ) + 1 / 2) * (Ex H.h H.x u σ) ^ ((H.n : ℝ) + 1 / 2))) s :=
    contDiffAt_const.mul hFx
  rw [hsplit, iteratedDeriv_add hA hB,
    iteratedDeriv_const_mul (-(deriv H.y σ)) hFy,
    iteratedDeriv_const_mul (-(deriv H.x σ)) hFx]
  ring

end Ident

end

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Commons.Geometry.Ulam (profileX semicircle)

noncomputable section

/-- The cofactor of the swept integrand (`Bfun`, defined in
`Submission.Work.OddVolterra.RowIdentity.WWDefs`) satisfies `Wint n h x y u σ =
(σ-u)^{n+1/2} · Bfun ... u σ`. -/
example (n : ℕ) (h x y : ℝ → ℝ) (u σ : ℝ) :
    Wint n h x y u σ = (σ - u) ^ ((n : ℝ) + 1 / 2) * Bfun n h x y u σ := rfl

section Setup

variable (H : Setup)

/-- `deriv` of a `C^∞` function on `(0,∞)` is `C^∞` there. -/
lemma contDiffOn_deriv_of_contDiffOn {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Set.Ioi 0)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (deriv g) (Set.Ioi 0) := by
  have hfd : ContDiffOn ℝ (⊤ : ℕ∞) (fderivWithin ℝ g (Set.Ioi 0)) (Set.Ioi 0) :=
    hg.fderivWithin (uniqueDiffOn_Ioi 0) (by simp)
  have hfd2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun σ => (fderivWithin ℝ g (Set.Ioi 0) σ) (1 : ℝ)) (Set.Ioi 0) :=
    hfd.clm_apply contDiffOn_const
  refine hfd2.congr (fun σ hσ => ?_)
  show deriv g σ = (fderivWithin ℝ g (Set.Ioi 0) σ) 1
  rw [fderivWithin_of_isOpen isOpen_Ioi hσ]
  rfl

/-- Joint smoothness of the cofactor `Bfun` on a rectangle of slopes. -/
lemma contDiffOn_Bfun {s δ : ℝ} (hδs : δ < s)
    (hQy : ∀ q : ℝ × ℝ, q ∈ Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (1 + δ) →
      0 < Qy H.h H.y q.1 q.2)
    (hQx : ∀ q : ℝ × ℝ, q ∈ Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (1 + δ) →
      0 < Qx H.h H.x q.1 q.2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => Bfun H.n H.h H.x H.y q.1 q.2)
      (Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (1 + δ)) := by
  set R : Set (ℝ × ℝ) := Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (1 + δ) with hR
  have hquot_j : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => hquot H.h q.1 q.2) := by
    rw [show (fun q : ℝ × ℝ => hquot H.h q.1 q.2)
        = fun q : ℝ × ℝ => dslope H.h q.1 q.2 from
      funext (fun q => hquot_eq_dslope H q.1 q.2)]
    exact Work.Analysis.Calculus.contDiff_dslope H.h H.hh
  have q_2_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => q.2) R := contDiff_snd.contDiffOn
  have q_1_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => q.1) R := contDiff_fst.contDiffOn
  have hh2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => H.h q.2) R :=
    (H.hh.comp contDiff_snd).contDiffOn
  have hh1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => H.h q.1) R :=
    (H.hh.comp contDiff_fst).contDiffOn
  have hmaps : MapsTo (fun q : ℝ × ℝ => q.2) R (Set.Ioi 0) := by
    intro q hq
    show 0 < q.2
    exact lt_trans (sub_pos.mpr hδs) hq.2.1
  have hyj : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => H.y q.2) R :=
    H.hy.comp q_2_smooth hmaps
  have hxj : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => H.x q.2) R :=
    H.hx.comp q_2_smooth hmaps
  have hdyj : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => deriv H.y q.2) R :=
    (contDiffOn_deriv_of_contDiffOn H.hy).comp q_2_smooth hmaps
  have hdxj : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => deriv H.x q.2) R :=
    (contDiffOn_deriv_of_contDiffOn H.hx).comp q_2_smooth hmaps
  have hQyj : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => Qy H.h H.y q.1 q.2) R := by
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => H.y q.2 + hquot H.h q.1 q.2) R :=
      hyj.add hquot_j.contDiffOn
    have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : ℝ × ℝ => line H.h q.2 (H.y q.2) + line H.h q.1 (H.y q.2)) R := by
      unfold line
      exact ((q_2_smooth.mul hyj).add hh2).add ((q_1_smooth.mul hyj).add hh1)
    unfold Qy
    exact h1.mul h2
  have hQxj : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => Qx H.h H.x q.1 q.2) R := by
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => -(H.x q.2) + hquot H.h q.1 q.2) R :=
      hxj.neg.add hquot_j.contDiffOn
    have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : ℝ × ℝ => line H.h q.2 (-(H.x q.2)) + line H.h q.1 (-(H.x q.2))) R := by
      unfold line
      exact ((q_2_smooth.mul hxj.neg).add hh2).add ((q_1_smooth.mul hxj.neg).add hh1)
    unfold Qx
    exact h1.mul h2
  have hp1 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => (Qy H.h H.y q.1 q.2) ^ ((H.n : ℝ) + 1 / 2)) R :=
    hQyj.rpow contDiffOn_const (fun q hq => ne_of_gt (hQy q hq))
  have hp2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => (Qx H.h H.x q.1 q.2) ^ ((H.n : ℝ) + 1 / 2)) R :=
    hQxj.rpow contDiffOn_const (fun q hq => ne_of_gt (hQx q hq))
  unfold Bfun
  exact (hp1.mul hdyj.neg).add (hp2.mul hdxj.neg)

/-- The `(n+1)`-st derivative of the swept part is the integral of the pointwise derivatives. -/
lemma iteratedDeriv_WW (s : ℝ) (hs : s ∈ Set.Icc H.a H.c) {δ : ℝ} (hδ : 0 < δ) (hδs : δ < s)
    (hQy : ∀ q : ℝ × ℝ, q ∈ Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (1 + δ) →
      0 < Qy H.h H.y q.1 q.2)
    (hQx : ∀ q : ℝ × ℝ, q ∈ Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (1 + δ) →
      0 < Qx H.h H.x q.1 q.2) :
    iteratedDeriv (H.n + 1) (WW H.n H.h H.x H.y) s
      = ∫ σ in s..1, iteratedDeriv (H.n + 1)
          (fun u : ℝ => (σ - u) ^ ((H.n : ℝ) + 1 / 2) * Bfun H.n H.h H.x H.y u σ) s := by
  have hs1 : s < 1 := lt_of_le_of_lt hs.2 H.hc1
  have hA := contDiffOn_Bfun H hδs hQy hQx
  have h := Work.Analysis.Abel.swept_iteratedDeriv_rpow H.n hs1 hδ hA
  rwa [← show (WW H.n H.h H.x H.y)
      = fun u : ℝ => ∫ σ in u..1, (σ - u) ^ ((H.n : ℝ) + 1 / 2) * Bfun H.n H.h H.x H.y u σ
      from rfl] at h

end Setup

end

/-! ## The row identity -/

/-- **The odd first-moment row identity** (Ryabogin, Annals 195 (2022), the system `(t1)`):
the `(n+1)`-st derivative of the first moment integral `momentF` is `E1` plus the Abel-type
integral of the kernel `Kvec`. -/
theorem odd_rowF (n : ℕ) (hn : 1 ≤ n) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (hc1 : c < 1)
    {h x y f : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hx : ContDiffOn ℝ (⊤ : ℕ∞) x (Set.Ioi 0)) (hy : ContDiffOn ℝ (⊤ : ℕ∞) y (Set.Ioi 0))
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioo (-1 : ℝ) 1))
    (hxy : ∀ u ∈ Set.Ioc (0 : ℝ) 1,
      f (y u) = u * y u + h u ∧ f (-(x u)) = -(u * (-(x u)) + h u))
    (hxdec : ∀ σ ∈ Set.Ioo a 1, deriv x σ ≤ 0) (hydec : ∀ σ ∈ Set.Ioo a 1, deriv y σ ≤ 0)
    (hxb : x 1 = Commons.Geometry.Ulam.profileX 1)
    (hyb : y 1 = Commons.Geometry.Ulam.profileX 1)
    (hfb : ∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1),
      f t = Commons.Geometry.Ulam.semicircle t)
    (hxle : ∀ s ∈ Set.Icc a 1, x 1 ≤ x s) (hyle : ∀ s ∈ Set.Icc a 1, y 1 ≤ y s)
    (hord : -x 1 ≤ y 1)
    (hint : ∀ s ∈ Set.Icc a 1, -(x s) ∈ Set.Ioo (-1 : ℝ) 1 ∧ y s ∈ Set.Ioo (-1 : ℝ) 1)
    (hKden : ∀ s σ : ℝ, a ≤ s → s ≤ σ → σ ≤ 1 →
      0 < (y σ + hquot h s σ) * (line h σ (y σ) + line h s (y σ)) ∧
      0 < (-(x σ) + hquot h s σ) * (line h σ (-(x σ)) + line h s (-(x σ))))
    (hmid : ∀ s ∈ Set.Icc a 1, ∀ t ∈ Set.Ioo (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1),
      0 < psi h Commons.Geometry.Ulam.semicircle s t)
    {s : ℝ} (hs : s ∈ Set.Icc a c) :
    iteratedDeriv (n + 1) (fun u : ℝ => momentF n h x y f u) s =
      E1 n h s + ∫ σ in s..1,
        (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 / Real.sqrt (σ - s) := by
  let H : Setup :=
    { n := n, hn := hn, a := a, c := c, ha := ha, hac := hac, hc1 := hc1,
      h := h, x := x, y := y, f := f, hh := hh, hx := hx, hy := hy, hf := hf, hxy := hxy,
      hxdec := hxdec, hydec := hydec, hxb := hxb, hyb := hyb, hfb := hfb, hxle := hxle,
      hyle := hyle, hord := hord, hint := hint,
      hKden := fun s σ hs' hsσ hσ1 => ⟨(hKden s σ hs' hsσ hσ1).1, (hKden s σ hs' hsσ hσ1).2⟩,
      hmid := hmid }
  have hs' : s ∈ Set.Icc H.a H.c := hs
  have hs1 : s < 1 := lt_of_le_of_lt hs.2 hc1
  have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
  obtain ⟨δQ, hδQpos, hQrect⟩ := Qy_Qx_rect_pos H hs'
  obtain ⟨δB, hδBpos, c₀, d₀, hc₀, hc₀d₀, hd₀, hboxB⟩ := section_box H hs'
  set δ : ℝ := min (min δQ δB) (min (s / 2) ((1 - s) / 2)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min hδQpos hδBpos) (lt_min (by linarith) (by linarith))
  have hδQ : δ ≤ δQ := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδB : δ ≤ δB := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδs : δ ≤ s / 2 := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ1 : δ ≤ (1 - s) / 2 := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  -- the split of the section integral
  have hev : (fun u : ℝ => momentF n h x y f u) =ᶠ[𝓝 s]
      (fun u => AA n h u + WW n h x y u) := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds s hδpos) (fun u hu => ?_)
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hu
    have hu_pos : 0 < u := by linarith [hu.1, hδs, hs0]
    have hu1 : u ≤ 1 := by linarith [hu.2, hδ1, hs1]
    have hus : s - δB < u := by linarith [hu.1]
    show momentF n h x y f u = AA n h u + WW n h x y u
    refine momentF_eq_AA_add_WW H (c := c₀) (d := d₀) hu_pos hu1 ?_ ?_ ?_ ?_ ?_
    · have hfcont : ContinuousOn H.f (Set.Icc c₀ d₀) :=
        (H.hf.continuousOn).mono
          (fun t ht => ⟨by linarith [ht.1, hc₀], by linarith [ht.2, hd₀]⟩)
      have hpsi : ContinuousOn (fun t : ℝ => psi H.h H.f u t) (Set.Icc c₀ d₀) := by
        unfold psi line
        exact (hfcont.pow 2).sub (((continuousOn_const.mul continuousOn_id).add
          continuousOn_const).pow 2)
      exact (hpsi.pow n).mul hpsi.sqrt
    · intro σ hσ
      exact hboxB σ ⟨by linarith [hσ.1, hus], hσ.2⟩
    · intro σ hσ
      exact H.hxy σ ⟨lt_of_lt_of_le hu_pos hσ.1.le, hσ.2⟩
    · intro σ hσ
      exact (hQrect (u, σ) ⟨⟨by linarith [hu.1, hδQ], by linarith [hu.2, hδQ]⟩,
        ⟨by linarith [hσ.1, hδQ, hu.1], by linarith [hσ.2]⟩⟩).1
    · intro σ hσ
      exact (hQrect (u, σ) ⟨⟨by linarith [hu.1, hδQ], by linarith [hu.2, hδQ]⟩,
        ⟨by linarith [hσ.1, hδQ, hu.1], by linarith [hσ.2]⟩⟩).2
  -- positivity on the smaller rectangle
  have hQyδ : ∀ q : ℝ × ℝ, q ∈ Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (1 + δ) →
      0 < Qy H.h H.y q.1 q.2 := by
    intro q hq
    exact (hQrect q ⟨⟨by linarith [hq.1.1, hδQ], by linarith [hq.1.2, hδQ]⟩,
      ⟨by linarith [hq.2.1, hδQ], by linarith [hq.2.2, hδQ]⟩⟩).1
  have hQxδ : ∀ q : ℝ × ℝ, q ∈ Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (1 + δ) →
      0 < Qx H.h H.x q.1 q.2 := by
    intro q hq
    exact (hQrect q ⟨⟨by linarith [hq.1.1, hδQ], by linarith [hq.1.2, hδQ]⟩,
      ⟨by linarith [hq.2.1, hδQ], by linarith [hq.2.2, hδQ]⟩⟩).2
  -- smoothness of the two pieces, for the sum rule
  have hAA : ContDiffAt ℝ (↑(n + 1)) (AA n h) s := contDiffAt_AA H hs'
  have hWWs : ContDiffAt ℝ (↑(n + 1)) (WW n h x y) s :=
    contDiffAt_WW H hs' hδpos (fun q hq => hQyδ q hq) (fun q hq => hQxδ q hq)
  have hsum : iteratedDeriv (n + 1) (fun u : ℝ => momentF n h x y f u) s
      = iteratedDeriv (n + 1) (AA n h) s + iteratedDeriv (n + 1) (WW n h x y) s := by
    rw [hev.iteratedDeriv_eq (n + 1)]
    exact iteratedDeriv_add hAA hWWs
  -- the value of the swept part
  have hWWval : iteratedDeriv (n + 1) (WW n h x y) s
      = ∫ σ in s..1,
          (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 / Real.sqrt (σ - s) := by
    rw [iteratedDeriv_WW H s hs' hδpos (by linarith [hδs, hs0]) (fun q hq => hQyδ q hq)
      (fun q hq => hQxδ q hq)]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun σ hσ => ?_))
    rw [Set.uIoc_of_le (le_of_lt hs1)] at hσ
    have hσ0 : 0 < σ := lt_trans hs0 hσ.1
    have hsσ : s < σ := hσ.1
    have hQy_ev : ∃ ε > 0, ∀ u : ℝ, |u - s| < ε → 0 < Ey H.h H.y u σ := by
      refine ⟨δQ, hδQpos, fun u hu => ?_⟩
      rw [abs_lt] at hu
      exact (hQrect (u, σ) ⟨⟨by linarith [hu.1], by linarith [hu.2]⟩,
        ⟨by linarith [hsσ, hδQpos], by linarith [hσ.2]⟩⟩).1
    have hQx_ev : ∃ ε > 0, ∀ u : ℝ, |u - s| < ε → 0 < Ex H.h H.x u σ := by
      refine ⟨δQ, hδQpos, fun u hu => ?_⟩
      rw [abs_lt] at hu
      exact (hQrect (u, σ) ⟨⟨by linarith [hu.1], by linarith [hu.2]⟩,
        ⟨by linarith [hsσ, hδQpos], by linarith [hσ.2]⟩⟩).2
    have hQyσ : 0 < Ey H.h H.y s σ :=
      (hQrect (s, σ) ⟨⟨by linarith [hδQpos], by linarith [hδQpos]⟩,
        ⟨by linarith [hsσ, hδQpos], by linarith [hσ.2]⟩⟩).1
    have hQxσ : 0 < Ex H.h H.x s σ :=
      (hQrect (s, σ) ⟨⟨by linarith [hδQpos], by linarith [hδQpos]⟩,
        ⟨by linarith [hsσ, hδQpos], by linarith [hσ.2]⟩⟩).2
    exact (kvec_ident H s σ hσ0 hσ.2 hsσ hQy_ev hQx_ev hQyσ hQxσ).symm
  rw [hsum, iteratedDeriv_AA H s hs', hWWval]

end Work.OddVolterra.RowIdentity
