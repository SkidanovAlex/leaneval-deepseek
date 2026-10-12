import ChallengeDeps
import Submission.Work.BoseFixB1B.boxM2_g2_le_nested_bareV
import Submission.Work.BoseFixB1S.mfM2_sub_mfM1_ge_const_mul_mfM1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.bareVPairMassExcess`

The mass-excess inequality for the **bare-`v`** localised pair kernel of FS `eq:HBU`:
there are `ε₀ > 0` and `c₀ > 0` such that at every admissible `μ` (`Adm v ε₀ μ`) and every
sliding position `u`,

    c₀ · ∬ w_{1,B(u)}  ≤  (∬ w_{B(u)}[v])  −  (∬ w_{1,B(u)}) ,

i.e. the *bare-`v`* pair mass exceeds the one-body mass `w₁ = w[g₀]` by a definite fraction of
`w₁`.  This is the mass comparison of FS `lm:w2>w1` in the shape the rung-4 accounting consumes:
the pair block of `boxQSum` (which uses the bare-`v` kernel, `Submission.Work.LocRepoint`) pays
the `w₁`-credit.

## Route (three machine-checked inputs, no new analysis)

Write `A := dlBox ℓ d u`, `ℓ := sideAt μ (a v)`, `d := (paramsAt μ (a v)).d` and

* `F := wSmallPair M ℓ d u (g₀ v h)` (the one-body kernel, `g₀ = v(1−ω₀)`),
* `G := wSmallPair M ℓ d u (g₂ v h)` (the FS two-body kernel, `g₂ = g₀(1+ω₀)`),
* `K := wSmallPair M ℓ d u v` (the **bare-`v`** kernel).

1. `Work.BoseFixB1S.mfM2M1_key` (the `ω₀`-mass identity of
   `Work.BoseFixB1B.boxM2_sub_boxM1_eq_omegaMass` plus the a.e. sandwich
   `c₀ F ≤ ω₀ F ≤ F`) gives

       c₀ · boxM1 ℓ A w₁  ≤  boxM2 (boxMass ℓ d u) A G  −  boxM1 ℓ A w₁ ,
       c₀ = (a v)/(2R).

2. `boxM1 ℓ A w₁ = ∬ w_{1,B(u)}` — the iterated integral defining `Work.BoseFixB1.w1MassB`
   (`Work.BoseFixB1S.boxM1_eq_nested` + the support collapse
   `Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox`).

3. `boxM2 (boxMass ℓ d u) A G ≤ ∬ K` — the bare-`v` kernel dominates `G` pointwise
   (`wSmallPair_mono_of_le` at `g₂ = v(1−ω₀²) ≤ v`, using `0 ≤ v` only), and the dilute regime
   `R ≤ ℓd/16`, `R ≤ ℓ·chiR0` (both supplied by `Work.BoseFixB1.regime_sideAt_ge` once `ε₀` is
   small) makes the bare-`v` kernel integrable on the big box, so the comparison integrates.

Adding the two displays and using (2) on both sides yields the claim with the *same* `c₀` and
`ε₀` as in (1).

The diluteness threshold `ε₀` is chosen as the `regime_sideAt_ge` bound at the *fixed* support
radius `R`; nothing else in the proof depends on `μ` except through `Adm`.
-/

namespace Work.BoseFixB1B

theorem bareVPairMassExcess {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) (hav : 0 < _root_.BoseGases.a v) {M : ℕ} (hM : 1 ≤ M) :
    ∃ ε₀ c₀ : ℝ, 0 < ε₀ ∧ 0 < c₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ u : EuclideanSpace ℝ (Fin 3),
        c₀ * Work.BoseFixB1.w1MassB h M (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          ≤ (∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
              Submission.BoseGases.wSmallPair M (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v x y)
            - Work.BoseFixB1.w1MassB h M (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u := by
  classical
  -- the diluteness threshold at the fixed support radius `R`
  obtain ⟨εreg, hεreg_pos, hεreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨εreg, _root_.BoseGases.a v / (2 * R), hεreg_pos, div_pos hav (by linarith), ?_⟩
  intro μ hAdm u
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
    Work.BoseFixB1.adm_d_pos hAdm
  obtain ⟨hR16, hRχ⟩ := hεreg μ (Work.BoseFixB1.adm_mu_pos hAdm) (Work.BoseFixB1.adm_dilute hAdm)
  -- (2) the one-body mass is the box fibre mass
  have hM1 : Work.BoseFixB1.w1MassB h M (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      = Work.BoseFixB1S.boxM1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (Submission.BoseGases.wSmall1Pair h M (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) := by
    rw [Work.BoseFixB1S.boxM1_eq_nested (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) u
      (w := Submission.BoseGases.wSmall1Pair h M (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (fun x y hxy => Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u hxy)]
    rfl
  -- (1) the `ω₀`-mass identity in its quantitative (`c₀`-form) shape
  have hbox := Work.BoseFixB1S.mfM2M1_key (v := v) (R := R) hv_supp hR hv hvrad hv1 h hav
    (M' := M) hM (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) hℓ hd u
  -- (3) the bare-`v` kernel dominates the `g₂`-kernel
  have hbare : Work.BoseFixB1S.boxM2
        (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Submission.BoseGases.wSmallPair M (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Submission.BoseGases.g2 v h))
      ≤ ∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wSmallPair M (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v x y :=
    boxM2_g2_le_nested_bareV (v := v) (R := R) hv_supp hR hv hvrad hv1 h (M := M) hM
      hℓ hd hR16 hRχ u
  rw [hM1]
  linarith

end Work.BoseFixB1B
