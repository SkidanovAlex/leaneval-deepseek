import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicTowerKit
import Submission.Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM_bndV
import Submission.Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM_addArg
import Submission.Work.Diff.EXT.ConnCov.RicFlip.HonestFlip

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.Diff.EXT.ConnCov.RicTr

/-! ## The kit for the sharpening

Three ingredients:

* `deltaTowerM_eq_vtower`: the moving `δ`-tower of the `RicFlip` chapter is the metric-indexed
  tower `vtower (G t) (deltaOf (G 0) (G t))` of `RicTowerKit` (the two recursions have the same
  bodies);
* `deltaTowerM_smul_val₂` / `deltaTowerM_smul_val₃`: the tower is homogeneous of degree one in each
  of its two value slots over *natural* coefficients, obtained from the additivity
  `RicFlip.deltaTowerM_addArg`;
* `sqrt_inner_smul`, `sqrt_inner_smul_mul`: the elementary `√⟨c•u,c•u⟩ = c√⟨u,u⟩` for `c ≥ 0`. -/

section SharpMovementKit

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- `√⟪c u, c u⟫ = c √⟪u,u⟫` for `c ≥ 0`. -/
lemma sqrt_inner_smul (g : Submission.Diff.SMet I M) (x : M) (c : ℝ) (hc : 0 ≤ c)
    (u : TangentSpace I x) :
    Real.sqrt (g.inner x (c • u) (c • u)) = c * Real.sqrt (g.inner x u u) := by
  rw [show g.inner x (c • u) (c • u) = c * c * g.inner x u u from by
      simp only [map_smul, smul_apply, smul_eq_mul]; ring,
    show c * c * g.inner x u u = (c * c) * g.inner x u u from rfl,
    Real.sqrt_mul (by positivity) (g.inner x u u),
    Real.sqrt_mul_self (by positivity : (0 : ℝ) ≤ c)]

/-- The iterated form of `sqrt_inner_smul`. -/
lemma sqrt_inner_smul_mul (g : Submission.Diff.SMet I M) (x : M) (c d : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (u : TangentSpace I x) :
    Real.sqrt (g.inner x (c • (d • u)) (c • (d • u))) = c * d * Real.sqrt (g.inner x u u) := by
  rw [← mul_smul]
  exact sqrt_inner_smul g x (c * d) (mul_nonneg hc hd) u

/-- The moving `δ`-tower is the `RicTowerKit` metric-indexed tower of the connection difference. -/
theorem deltaTowerM_eq_vtower (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (c : ℕ) :
    Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t c
      = Work.Diff.EXT.ConnCov.vtower (G t)
          (fun _ X Y => Work.Diff.EXT.ConnCov.deltaOf (G 0) (G t) X Y) c := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [show Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t (c + 1)
          = Work.Diff.EXT.ConnCov.RicFlip.vstepM (G t)
              (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t c) from rfl,
        show Work.Diff.EXT.ConnCov.vtower (G t)
              (fun _ X Y => Work.Diff.EXT.ConnCov.deltaOf (G 0) (G t) X Y) (c + 1)
          = Work.Diff.EXT.ConnCov.vstep (G t)
              (Work.Diff.EXT.ConnCov.vtower (G t)
                (fun _ X Y => Work.Diff.EXT.ConnCov.deltaOf (G 0) (G t) X Y) c) from rfl,
        ih]
    rfl

/-- Natural homogeneity of the moving `δ`-tower in its **second** value slot: the tower is additive
in that slot (`RicFlip.deltaTowerM_addArg`) on smooth fields, hence homogeneous for natural
coefficients by induction. -/
theorem deltaTowerM_smul_val₂ (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (c : ℕ) :
    ∀ n : ℕ, 1 ≤ n → ∀ (v : Fin c → Work.Diff.EXT.ATower.TF (I := I) (M := M))
      (X Z : Work.Diff.EXT.ATower.TF (I := I) (M := M)) (x : M),
      (∀ i, Work.Diff.EXT.ATower.SmE I M (v i)) → Work.Diff.EXT.ATower.SmE I M X →
      Work.Diff.EXT.ATower.SmE I M Z →
      Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t c v ((n : ℝ) • X) Z x
        = (n : ℝ) • Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t c v X Z x := by
  intro n
  induction n with
  | zero => intro hn; exact absurd hn (by omega)
  | succ n ih =>
    intro hn v X Z x hv hX hZ
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      have h1 : (((0 + 1 : ℕ)) : ℝ) = 1 := by norm_num
      rw [h1]
      simp only [one_smul]
    · have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      have ih' := ih (by omega) v X Z x hv hX hZ
      have hadd := Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM_addArg (I := I) (M := M) hLC G t c
      have hsm : Work.Diff.EXT.ATower.SmE I M ((n : ℝ) • X) :=
        ContMDiff.smul_section (contMDiff_const (c := (n : ℝ))) hX
      rw [hcast, add_smul, one_smul,
        hadd.2.1 v ((n : ℝ) • X) X Z hv hsm hX hZ x, ih']
      simp only [add_smul, one_smul]

/-- Natural homogeneity of the moving `δ`-tower in its **third** value slot. -/
theorem deltaTowerM_smul_val₃ (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (c : ℕ) :
    ∀ n : ℕ, 1 ≤ n → ∀ (v : Fin c → Work.Diff.EXT.ATower.TF (I := I) (M := M))
      (X Z : Work.Diff.EXT.ATower.TF (I := I) (M := M)) (x : M),
      (∀ i, Work.Diff.EXT.ATower.SmE I M (v i)) → Work.Diff.EXT.ATower.SmE I M X →
      Work.Diff.EXT.ATower.SmE I M Z →
      Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t c v X ((n : ℝ) • Z) x
        = (n : ℝ) • Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t c v X Z x := by
  intro n
  induction n with
  | zero => intro hn; exact absurd hn (by omega)
  | succ n ih =>
    intro hn v X Z x hv hX hZ
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      have h1 : (((0 + 1 : ℕ)) : ℝ) = 1 := by norm_num
      rw [h1]
      simp only [one_smul]
    · have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      have ih' := ih (by omega) v X Z x hv hX hZ
      have hadd := Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM_addArg (I := I) (M := M) hLC G t c
      have hsm : Work.Diff.EXT.ATower.SmE I M ((n : ℝ) • Z) :=
        ContMDiff.smul_section (contMDiff_const (c := (n : ℝ))) hZ
      rw [hcast, add_smul, one_smul,
        hadd.2.2 v X ((n : ℝ) • Z) Z hv hX hsm hZ x, ih']
      simp only [add_smul, one_smul]

end SharpMovementKit

/-- **Sharpening a `BndV` bound on the moving `δ`-tower into the `dvVal` shape.**  Given the
`AMB.BndV` bounds of `RicFlip.deltaTowerM` (`ConnCov/RicFlip/deltaTowerM_bndV.lean`), which are
`(1+√⟨·,·⟩)`-shaped,
  `√⟨Θ v X Z x, Θ v X Z x⟩ ≤ B c · ∏_i (1+√⟨v_i x, v_i x⟩) · (1+√⟨X x,X x⟩) · (1+√⟨Z x,Z x⟩)`,
produce the `dvVal`-shaped bounds with `√⟨X x,X x⟩ · √⟨Z x,Z x⟩` instead of the last two factors.

PROOF SKETCH.  `RicFlip.deltaTowerM G t c = RicFlip.vtowerM (G t) (deltaBaseM G t) c`, and
`RicFlip.vstepM`/`vtowerM` have the same bodies as the metric-indexed `vstep`/`vtower` of
`RicTowerKit`, while `RicFlip.deltaBaseM G t = deltaOf (G 0) (G t)`; bridge by induction.  The extra
content is the *linearity of the tower in its two value slots over (at least constant) coefficients*:
prove `Θ v (s • X) Z = s • Θ v X Z` and `Θ v X (t • Z) = t • Θ v X Z` as field identities by
induction on `c`, using the additivity of `vstep` in the value slots and the Leibniz rule of `lcOf`.
Then fix `v, X, Y, x`: if `X x = 0` or `Y x = 0` the tower value at `x` is `0` (value-dependence,
or linearity with the coefficient `0`), so the bound is trivial; otherwise set
`s := (√⟨X x,X x⟩)⁻¹`, `t := (√⟨Y x,Y y⟩)⁻¹`, apply `hBndV` to the sections `s • smoothExt x X` and
`t • smoothExt x Y` (constant multiples of smooth sections are smooth, and their norms at `x` are
`1`), and divide by `s·t`: this gives the target bound with `E c := 4 · B c`. -/
theorem sharpMovement_of_bndV
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hT : 0 < T)
    (k : ℕ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hBndV : ∀ c, c < k → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ConnCov.AMB.BndV G t (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t c) (B c)) :
    ∃ E : ℕ → ℝ, (∀ c, 0 ≤ E c) ∧ ∀ c, c < k → ∀ t ∈ Set.Ico (T / 2) T,
      (∀ (x : M) (v : Fin c → TangentSpace I x) (X Y : TangentSpace I x),
        Work.Diff.EXT.ConnCov.dvVal (G t)
            (Work.Diff.EXT.ConnCov.vtower (G t)
              (fun _ X Y => Work.Diff.EXT.ConnCov.deltaOf (G 0) (G t) X Y) c) x v X Y
          ≤ E c * (Work.Diff.EXT.ConnCov.oneAddSqrtProd (G t) x v
              * Real.sqrt ((G t).inner x X X) * Real.sqrt ((G t).inner x Y Y))) := by
  refine ⟨B, hB, ?_⟩
  intro c hc t ht x v X Y
  have hbndv := hBndV c hc t ht
  rw [← deltaTowerM_eq_vtower (I := I) (M := M) G t c]
  simp only [Work.Diff.EXT.ConnCov.dvVal, Work.Diff.EXT.ConnCov.oneAddSqrtProd]
  set vh : Fin c → Work.Diff.EXT.ATower.TF (I := I) (M := M) :=
    fun i => Submission.Diff.smoothExt x (v i) with hvh
  set Xh : Work.Diff.EXT.ATower.TF (I := I) (M := M) :=
    Submission.Diff.smoothExt x X with hXh
  set Yh : Work.Diff.EXT.ATower.TF (I := I) (M := M) :=
    Submission.Diff.smoothExt x Y with hYh
  set w : TangentSpace I x :=
    Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t c vh Xh Yh x with hw
  set P : ℝ := Finset.univ.prod (fun i : Fin c => 1 + Real.sqrt ((G t).inner x (v i) (v i)))
    with hPset
  set a : ℝ := Real.sqrt ((G t).inner x X X) with haset
  set b : ℝ := Real.sqrt ((G t).inner x Y Y) with hbset
  have hvh_sm : ∀ i, Work.Diff.EXT.ATower.SmE I M (vh i) :=
    fun i => Work.Diff.GE.smoothExt_cmdiff x (v i)
  have hXh_sm : Work.Diff.EXT.ATower.SmE I M Xh := Work.Diff.GE.smoothExt_cmdiff x X
  have hYh_sm : Work.Diff.EXT.ATower.SmE I M Yh := Work.Diff.GE.smoothExt_cmdiff x Y
  have hvap : ∀ i, vh i x = v i := fun i => Work.Diff.GE.smoothExt_apply x (v i)
  have hXap : Xh x = X := Work.Diff.GE.smoothExt_apply x X
  have hYap : Yh x = Y := Work.Diff.GE.smoothExt_apply x Y
  -- the scaled estimate, for every natural coefficient `n ≥ 1`
  have hstep : ∀ n : ℕ, 1 ≤ n →
      Real.sqrt ((G t).inner x w w)
        ≤ B c * P * (1 / (n : ℝ) + a) * (1 / (n : ℝ) + b) := by
    intro n hn
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hsmX : Work.Diff.EXT.ATower.SmE I M ((n : ℝ) • Xh) :=
      ContMDiff.smul_section (contMDiff_const (c := (n : ℝ))) hXh_sm
    have hsmY : Work.Diff.EXT.ATower.SmE I M ((n : ℝ) • Yh) :=
      ContMDiff.smul_section (contMDiff_const (c := (n : ℝ))) hYh_sm
    have hbv := hbndv vh ((n : ℝ) • Xh) ((n : ℝ) • Yh) hvh_sm hsmX hsmY x
    -- the tower value scales by `n` in each of the two value slots
    have htw : Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t c vh ((n : ℝ) • Xh) ((n : ℝ) • Yh) x
        = (n : ℝ) • ((n : ℝ) • w) := by
      rw [deltaTowerM_smul_val₃ (I := I) (M := M) hLC G t c n hn vh ((n : ℝ) • Xh) Yh x
            hvh_sm hsmX hYh_sm,
        deltaTowerM_smul_val₂ (I := I) (M := M) hLC G t c n hn vh Xh Yh x
            hvh_sm hXh_sm hYh_sm,
        ← hw]
    have hsq : Real.sqrt ((G t).inner x ((n : ℝ) • ((n : ℝ) • w)) ((n : ℝ) • ((n : ℝ) • w)))
        = (n : ℝ) * (n : ℝ) * Real.sqrt ((G t).inner x w w) :=
      sqrt_inner_smul_mul (G t) x (n : ℝ) (n : ℝ) hn0 hn0 w
    have hPa : Finset.univ.prod (fun i : Fin c => 1 + Real.sqrt ((G t).inner x (vh i x) (vh i x)))
        = P := by
      rw [hPset]
      exact Finset.prod_congr rfl (fun i _ => by rw [hvap i])
    have hna : Real.sqrt ((G t).inner x (((n : ℝ) • Xh) x) (((n : ℝ) • Xh) x)) = (n : ℝ) * a := by
      have h1 : ((n : ℝ) • Xh) x = (n : ℝ) • X := by rw [Pi.smul_apply, hXap]
      rw [h1, sqrt_inner_smul (G t) x (n : ℝ) hn0 X, ← haset]
    have hnb : Real.sqrt ((G t).inner x (((n : ℝ) • Yh) x) (((n : ℝ) • Yh) x)) = (n : ℝ) * b := by
      have h1 : ((n : ℝ) • Yh) x = (n : ℝ) • Y := by rw [Pi.smul_apply, hYap]
      rw [h1, sqrt_inner_smul (G t) x (n : ℝ) hn0 Y, ← hbset]
    rw [htw, hsq, hPa, hna, hnb] at hbv
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hid1 : (1 / (n : ℝ) + a) * (n : ℝ) = 1 + (n : ℝ) * a := by
      rw [add_mul, one_div, inv_mul_cancel₀ hnne]; ring
    have hid2 : (1 / (n : ℝ) + b) * (n : ℝ) = 1 + (n : ℝ) * b := by
      rw [add_mul, one_div, inv_mul_cancel₀ hnne]; ring
    have h2 : Real.sqrt ((G t).inner x w w) * ((n : ℝ) * (n : ℝ))
        ≤ (B c * P * (1 / (n : ℝ) + a) * (1 / (n : ℝ) + b)) * ((n : ℝ) * (n : ℝ)) := by
      calc Real.sqrt ((G t).inner x w w) * ((n : ℝ) * (n : ℝ))
          = (n : ℝ) * (n : ℝ) * Real.sqrt ((G t).inner x w w) := by ring
        _ ≤ B c * P * (1 + (n : ℝ) * a) * (1 + (n : ℝ) * b) := hbv
        _ = (B c * P * (1 / (n : ℝ) + a) * (1 / (n : ℝ) + b)) * ((n : ℝ) * (n : ℝ)) := by
            rw [← hid1, ← hid2]; ring
    exact le_of_mul_le_mul_right h2 (mul_pos hnpos hnpos)
  -- let the coefficient tend to infinity
  have htend : Filter.Tendsto (fun n : ℕ => B c * P * (1 / (n : ℝ) + a) * (1 / (n : ℝ) + b))
      Filter.atTop (nhds (B c * (P * a * b))) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h2 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ) + a) Filter.atTop (nhds (0 + a)) :=
      h1.add (tendsto_const_nhds (x := a))
    have h3 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ) + b) Filter.atTop (nhds (0 + b)) :=
      h1.add (tendsto_const_nhds (x := b))
    have h4 : Filter.Tendsto (fun n : ℕ => (B c * P) * ((1 / (n : ℝ) + a) * (1 / (n : ℝ) + b)))
        Filter.atTop (nhds ((B c * P) * ((0 + a) * (0 + b)))) := (h2.mul h3).const_mul (B c * P)
    simpa only [mul_assoc, zero_add] using h4
  have hmain : Real.sqrt ((G t).inner x w w) ≤ B c * (P * a * b) := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds htend ?_
    exact Filter.eventually_atTop.mpr ⟨1, fun n hn => hstep n hn⟩
  exact hmain

end Work.Diff.EXT.ConnCov.RicTr
