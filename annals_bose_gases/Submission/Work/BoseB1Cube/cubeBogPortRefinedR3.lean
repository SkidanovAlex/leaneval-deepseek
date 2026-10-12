import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.chainA2SharpRefined3
import Submission.Work.BoseB1Cube.cubeSmallNArb12
import Submission.Work.BoseB1Cube.sharpTerm1BoundRefined3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.cubeBogPortRefinedR3` — the refined cube Bogoliubov port **with the kept band
row** `R₃`

FS `eq:refinedaprioribog` keeps the band (`(dsℓ)⁻³`) row of the first-term bound as an *explicit*
row and pays it later by the state-independent row `Cμ²aΓ∫χ²` of `thm:smallbox`.  The corpus's
`bogPortRefinedCube` / `refinedCubePort` instead deleted that row, which is why their ledger needed
an *unbounded* constant `C ≳ (μa³)^{-1.5/323}` (see `FINDING_bogPortRefinedCube.md` §7 and
`FINDING_cubeSmallNArb12ExHolds.md` §3).  This module proves the port in the *kept*-`R₃` form: the
target's left side carries the third row

    − C·(a v)·(sbCut μ (a v))³·(n/|B(u)|)·chiMass

which is exactly the payer of the chain's `R₃`, with a **fixed** constant.

The proof combines the two PROVED bricks `chainA2SharpRefined3` (the sharp chain at the three-row
bracket) and `sharpTerm1BoundRefined3` (that bracket), and then the pure-real row arithmetic
`r3RowArith` below, whose three gates

* `hgate` — `R₁`/`R₂` together fit in the mass row (`r₁ + r₂ ≤ 1`),
* `hC3` — `Kc² ≤ 3π²K_s·C` (the credit pays `R₃`),
* `hC4` — `4K_s·κ_χ² ≤ C` (the credit pays the chain's own loss),

are all of the form "a fixed constant times a power of `X = (μa³)^{1/323}`, or a positive power of
`t` times a power of `log`, hence satisfiable with a *fixed* `(κ, C)` and a small `ε₀`.  The key
arithmetic identities at FS's parameters are

* `a·sbCut μ a = X^{156}` and `PBΓ v μ = X^{143.5}`, so `8·(a·c) ≤ 8Γ`;
* `(R/ℓ)² ≤ (R/a)²Γ`, `(R/(ℓd))² ≤ (R/a)²Γ` (from `ℓ = a·X^{-163}`, `ℓd = a·X^{-157}`);
* `1 + log((a·c)⁻¹) ≤ 1 + |log t|`, paid by `fsXp_mul_log_le_one` (a positive power of `t` beats
  every power of `log t`).
-/

namespace Work.BoseB1Cube

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal ContDiff

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.SmallBoxSliding Work.BoseBoxFix
  Work.BoseFixB1 Work.BoseFixB1S Work.BoseFixB1B

/-- **The pure-real row arithmetic of the kept-`R₃` port.**

With `S ≤ n` (the flat count), `J0 ≤ J1·D` (the Newtonian mass) and the three gates

* `hgate` — the `R₁`/`R₂` split, i.e. `r₁ + r₂ ≤ 1` after division by `1 + κΓ`,
* `hC3` — `Kc² ≤ 3π²K_s·C` (the credit pays `R₃`),
* `hC4` — `4K_s·κ_χ² ≤ C` (the credit pays the chain's own `A₁`-loss),

the sharp chain's rows are dominated by the target's rows. -/
private lemma r3RowArith
    {S X V D Kc Ks c av κ Γ C κχ J0 J1 n np μ : ℝ}
    (hX : 0 ≤ X) (hV : 0 < V) (hD : 0 < D) (hSle : S ≤ n) (hn0 : 0 ≤ n)
    (hKs : 0 < Ks) (hc : 0 < c) (hav : 0 ≤ av) (hκ : 0 ≤ κ) (hΓ0 : 0 ≤ Γ)
    (hKc : 0 ≤ Kc) (hκχ : 0 ≤ κχ) (hC : 0 ≤ C) (hnp : 0 ≤ np) (hμn : 0 ≤ μ + n / V)
    (hJ00 : 0 ≤ J0) (hJ0 : J0 ≤ J1 * D)
    (hL0 : 0 ≤ 1 + Real.log ((av * c)⁻¹))
    (hgate : (1 + 8 * (av * c)) * J1
        + 4 * c * Kc ^ 2 * av ^ 2 * (1 + Real.log ((av * c)⁻¹)) / (Real.pi ^ 2 * D)
        ≤ 2 * (1 + κ * Γ))
    (hC3 : Kc ^ 2 ≤ 3 * Real.pi ^ 2 * Ks * C)
    (hC4 : 4 * Ks * κχ ^ 2 ≤ C) :
    S * X * ((1 + 8 * (av * c)) * ((n + 1) / (4 * V ^ 2)) * J0
        + (1 / Real.pi ^ 2) * ((n + 1) * c * Kc ^ 2 * av ^ 2 / V ^ 2)
            * (1 + Real.log ((av * c)⁻¹))
        + (1 / (3 * Real.pi ^ 2)) * (Kc ^ 2 * av * c ^ 3 / (Ks * V)))
      + (4 * Ks * κχ ^ 2) * av * ((μ + n / V) * np)
    ≤ (1 / 2) * (1 + κ * Γ) * D * (((n + 1) * n) / V ^ 2) * X
      + C * av * (μ + n / V) * np + C * av * c ^ 3 * (n / V) * X := by
  have hV2 : (0:ℝ) < V^2 := pow_pos hV 2
  have hpi2 : (0:ℝ) < Real.pi^2 := pow_pos Real.pi_pos 2
  have h1κΓ : (0:ℝ) < 1 + κ * Γ := by linarith [mul_nonneg hκ hΓ0]
  set L : ℝ := 1 + Real.log ((av * c)⁻¹) with hLdef
  have hL0' : 0 ≤ L := by rw [hLdef]; exact hL0
  have hP0 : 0 ≤ (1 + 8 * (av * c)) * ((n + 1) / (4 * V ^ 2)) := by
    have h1 : 0 ≤ 1 + 8 * (av * c) := by nlinarith [mul_nonneg hav (le_of_lt hc)]
    have h2 : 0 ≤ (n + 1) / (4 * V ^ 2) := div_nonneg (by linarith) (by positivity)
    exact mul_nonneg h1 h2
  have hJ1D0 : 0 ≤ J1 * D := le_trans hJ00 hJ0
  have hJ10 : 0 ≤ J1 := by nlinarith [hJ1D0, hD]
  set M : ℝ := (1 / 2) * (1 + κ * Γ) * D * (((n + 1) * n) / V ^ 2) * X with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    have h2 : 0 ≤ ((n + 1) * n) / V ^ 2 := div_nonneg (by nlinarith) (le_of_lt hV2)
    have h1 : 0 ≤ (1 / 2) * (1 + κ * Γ) * D := by positivity
    exact mul_nonneg (mul_nonneg h1 h2) hX
  set θ : ℝ := (1 + 8 * (av * c)) * J1 / (2 * (1 + κ * Γ)) with hθdef
  set ρ : ℝ := 2 * c * Kc ^ 2 * av ^ 2 * L / (Real.pi ^ 2 * (1 + κ * Γ) * D) with hρdef
  -- #### row 1
  have hrow1 : S * X * ((1 + 8 * (av * c)) * ((n + 1) / (4 * V ^ 2)) * J0) ≤ θ * M := by
    have hstep : S * X * ((1 + 8 * (av * c)) * ((n + 1) / (4 * V ^ 2)) * J0)
        ≤ n * X * ((1 + 8 * (av * c)) * ((n + 1) / (4 * V ^ 2)) * (J1 * D)) := by
      have h1 : (1 + 8 * (av * c)) * ((n + 1) / (4 * V ^ 2)) * J0
          ≤ (1 + 8 * (av * c)) * ((n + 1) / (4 * V ^ 2)) * (J1 * D) :=
        mul_le_mul_of_nonneg_left hJ0 hP0
      have h2 : X * ((1 + 8 * (av * c)) * ((n + 1) / (4 * V ^ 2)) * J0)
          ≤ X * ((1 + 8 * (av * c)) * ((n + 1) / (4 * V ^ 2)) * (J1 * D)) :=
        mul_le_mul_of_nonneg_left h1 hX
      have h3 : S * (X * ((1 + 8 * (av * c)) * ((n + 1) / (4 * V ^ 2)) * J0))
          ≤ n * (X * ((1 + 8 * (av * c)) * ((n + 1) / (4 * V ^ 2)) * (J1 * D))) :=
        mul_le_mul hSle h2 (mul_nonneg hX (mul_nonneg hP0 hJ00)) hn0
      calc S * X * ((1 + 8 * (av * c)) * ((n + 1) / (4 * V ^ 2)) * J0)
          = S * (X * ((1 + 8 * (av * c)) * ((n + 1) / (4 * V ^ 2)) * J0)) := by ring
        _ ≤ n * (X * ((1 + 8 * (av * c)) * ((n + 1) / (4 * V ^ 2)) * (J1 * D))) := h3
        _ = n * X * ((1 + 8 * (av * c)) * ((n + 1) / (4 * V ^ 2)) * (J1 * D)) := by ring
    refine le_trans hstep ?_
    rw [hθdef, hMdef]
    refine le_of_eq ?_
    field_simp
    ring
  -- #### row 2
  have hrow2 : S * X * ((1 / Real.pi ^ 2) * ((n + 1) * c * Kc ^ 2 * av ^ 2 / V ^ 2) * L)
      ≤ ρ * M := by
    have hpos : 0 ≤ (1 / Real.pi ^ 2) * ((n + 1) * c * Kc ^ 2 * av ^ 2 / V ^ 2) * L := by
      refine mul_nonneg ?_ hL0'
      exact mul_nonneg (by positivity) (by positivity)
    have h1 : S * X * ((1 / Real.pi ^ 2) * ((n + 1) * c * Kc ^ 2 * av ^ 2 / V ^ 2) * L)
        ≤ n * X * ((1 / Real.pi ^ 2) * ((n + 1) * c * Kc ^ 2 * av ^ 2 / V ^ 2) * L) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSle hX) hpos
    refine le_trans h1 ?_
    rw [hρdef, hMdef]
    refine le_of_eq ?_
    field_simp
  -- #### row 3
  have hrow3 : S * X * ((1 / (3 * Real.pi ^ 2)) * (Kc ^ 2 * av * c ^ 3 / (Ks * V)))
      ≤ (Kc ^ 2 / (3 * Real.pi ^ 2 * Ks)) * (av * c ^ 3 * (n / V) * X) := by
    have hpos : 0 ≤ (1 / (3 * Real.pi ^ 2)) * (Kc ^ 2 * av * c ^ 3 / (Ks * V)) :=
      mul_nonneg (by positivity) (div_nonneg (by positivity) (by positivity))
    have h1 : S * X * ((1 / (3 * Real.pi ^ 2)) * (Kc ^ 2 * av * c ^ 3 / (Ks * V)))
        ≤ n * X * ((1 / (3 * Real.pi ^ 2)) * (Kc ^ 2 * av * c ^ 3 / (Ks * V))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSle hX) hpos
    refine le_trans h1 (le_of_eq ?_)
    field_simp
  have hr3le : Kc ^ 2 / (3 * Real.pi ^ 2 * Ks) ≤ C := by
    rw [div_le_iff₀ (by positivity)]
    linarith [hC3]
  have hrow3' : S * X * ((1 / (3 * Real.pi ^ 2)) * (Kc ^ 2 * av * c ^ 3 / (Ks * V)))
      ≤ C * av * c ^ 3 * (n / V) * X := by
    have h2 : (Kc ^ 2 / (3 * Real.pi ^ 2 * Ks)) * (av * c ^ 3 * (n / V) * X)
        ≤ C * (av * c ^ 3 * (n / V) * X) :=
      mul_le_mul_of_nonneg_right hr3le (by positivity)
    have h3 : C * (av * c ^ 3 * (n / V) * X) = C * av * c ^ 3 * (n / V) * X := by ring
    linarith [hrow3, h2, h3.le, h3.ge]
  -- #### the credit row
  have hcred : (4 * Ks * κχ ^ 2) * av * ((μ + n / V) * np) ≤ C * av * (μ + n / V) * np := by
    have h2 : (4 * Ks * κχ ^ 2) * (av * ((μ + n / V) * np)) ≤ C * (av * ((μ + n / V) * np)) :=
      mul_le_mul_of_nonneg_right hC4 (by positivity)
    calc (4 * Ks * κχ ^ 2) * av * ((μ + n / V) * np)
        = (4 * Ks * κχ ^ 2) * (av * ((μ + n / V) * np)) := by ring
      _ ≤ C * (av * ((μ + n / V) * np)) := h2
      _ = C * av * (μ + n / V) * np := by ring
  -- #### the two ratio bounds
  have hθρ : θ + ρ ≤ 1 := by
    have hnum : (1 + 8 * (av * c)) * J1 * (Real.pi ^ 2 * D) + 4 * c * Kc ^ 2 * av ^ 2 * L
        - 2 * (1 + κ * Γ) * (Real.pi ^ 2 * D) ≤ 0 := by
      have h3 : ((1 + 8 * (av * c)) * J1 + 4 * c * Kc ^ 2 * av ^ 2 * L / (Real.pi ^ 2 * D))
          * (Real.pi ^ 2 * D) ≤ 2 * (1 + κ * Γ) * (Real.pi ^ 2 * D) :=
        mul_le_mul_of_nonneg_right hgate (by positivity)
      have h4 : ((1 + 8 * (av * c)) * J1 + 4 * c * Kc ^ 2 * av ^ 2 * L / (Real.pi ^ 2 * D))
          * (Real.pi ^ 2 * D)
          = (1 + 8 * (av * c)) * J1 * (Real.pi ^ 2 * D) + 4 * c * Kc ^ 2 * av ^ 2 * L := by
        field_simp
      linarith [h3, h4.le, h4.ge]
    have hsplit : θ + ρ - 1 = ((1 + 8 * (av * c)) * J1 * (Real.pi ^ 2 * D)
        + 4 * c * Kc ^ 2 * av ^ 2 * L - 2 * (1 + κ * Γ) * (Real.pi ^ 2 * D))
        / (2 * (1 + κ * Γ) * (Real.pi ^ 2 * D)) := by
      rw [hθdef, hρdef]
      field_simp
      ring
    have h0 : θ + ρ - 1 ≤ 0 := by
      rw [hsplit]
      exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
    linarith
  -- #### assembly
  have hA12 : S * X * ((1 + 8 * (av * c)) * ((n + 1) / (4 * V ^ 2)) * J0)
      + S * X * ((1 / Real.pi ^ 2) * ((n + 1) * c * Kc ^ 2 * av ^ 2 / V ^ 2) * L) ≤ M := by
    have h1 : S * X * ((1 + 8 * (av * c)) * ((n + 1) / (4 * V ^ 2)) * J0)
        + S * X * ((1 / Real.pi ^ 2) * ((n + 1) * c * Kc ^ 2 * av ^ 2 / V ^ 2) * L)
        ≤ θ * M + ρ * M := by linarith [hrow1, hrow2]
    have h2 : θ * M + ρ * M = (θ + ρ) * M := by ring
    have h3 : (θ + ρ) * M ≤ M := by
      have := mul_le_mul_of_nonneg_right hθρ hM0
      simpa using this
    linarith [h1, h2.le, h2.ge, h3]
  have hdist : S * X * ((1 + 8 * (av * c)) * ((n + 1) / (4 * V ^ 2)) * J0
        + (1 / Real.pi ^ 2) * ((n + 1) * c * Kc ^ 2 * av ^ 2 / V ^ 2) * L
        + (1 / (3 * Real.pi ^ 2)) * (Kc ^ 2 * av * c ^ 3 / (Ks * V)))
      = S * X * ((1 + 8 * (av * c)) * ((n + 1) / (4 * V ^ 2)) * J0)
        + S * X * ((1 / Real.pi ^ 2) * ((n + 1) * c * Kc ^ 2 * av ^ 2 / V ^ 2) * L)
        + S * X * ((1 / (3 * Real.pi ^ 2)) * (Kc ^ 2 * av * c ^ 3 / (Ks * V))) := by ring
  rw [hdist]
  linarith [hA12, hrow3', hcred]

theorem cubeBogPortRefinedR3 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ κ C : ℝ, 0 < ε₀ ∧ 0 ≤ κ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
          1 ≤ n → ContDiff ℝ (⊤ : ℕ∞) Φ →
          (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Φ x) ^ 2) = 1 →
          -((1 / 2) * (1 + κ * Work.BoseFixB1B.PBΓ v μ) * Submission.BoseGases.g0w0Mass h
                * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
                * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bD v μ) u
              + C * (_root_.BoseGases.a v)
                  * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
                  * Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
                      (Work.BoseFixB1.bV v μ u) Φ
              + C * (_root_.BoseGases.a v) * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
                  * ((n : ℝ) / Work.BoseFixB1.bV v μ u)
                  * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                      (Work.BoseFixB1.bD v μ) u)
          ≤ Work.BoseFixB1S.bSpectralCube v μ Φ u + Work.BoseFixB1.bA2 v h μ Φ u := by
  classical
  -- ### the constants supplied by the corpus
  obtain ⟨Kc, hKc0, hKcbound⟩ :=
    Work.BoseFixB1S.nuPairWNuIntegrable (v := v) h hv hv1 hvrad hR hv_supp hav
      (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
  obtain ⟨K1s, hK1s0, hK1sh⟩ :=
    Work.BoseFixB1S.slidingNewtonMassSharpB1 (v := v) (R := R) hv_supp hR hv hvrad hv1 h
      (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
  obtain ⟨ε₁, hε₁pos, hreg⟩ :=
    Work.BoseFixB1S.admGoodSetRegime2 (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨ε₃, hε₃pos, hε₃val⟩ := Work.BoseFixGlue.Pot.ellB_ge (v := v) hav hR
  set D : ℝ := Submission.BoseGases.g0w0Mass (v := v) h with hDdef
  have hDpos : 0 < D := by
    rw [hDdef, ← Work.BoseFixB1B.PairMass_eq_g0w0Mass]
    exact Work.BoseFixB1B.pairMass_pos h hR hv hv1 hvrad hv_supp hav
  set κχ : ℝ := Submission.BoseGases.chiSupAbs
    * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue with hκχdef
  have hκχ0 : 0 ≤ κχ :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg _)
  set Ks : ℝ := max 1 (Kc / 2) with hKsdef
  have hKs0 : 0 < Ks := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hKsKc : Kc ≤ 2 * Ks := by
    have h1 : Kc / 2 ≤ Ks := le_max_right _ _
    linarith
  set C₀ : ℝ := max (4 * Ks * κχ ^ 2) (Kc ^ 2 / (3 * Real.pi ^ 2 * Ks)) with hC₀def
  have hC₀0 : 0 ≤ C₀ := by
    rw [hC₀def]
    exact le_max_of_le_left (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hKs0)) (sq_nonneg κχ))
  have hC₀C4 : 4 * Ks * κχ ^ 2 ≤ C₀ := le_max_left _ _
  have hC₀C3 : Kc ^ 2 ≤ 3 * Real.pi ^ 2 * Ks * C₀ := by
    have h1 : Kc ^ 2 / (3 * Real.pi ^ 2 * Ks) ≤ C₀ := le_max_right _ _
    rw [div_le_iff₀ (by positivity)] at h1
    linarith [h1]
  set εd : ℝ := (1 / 2 : ℝ) ^ ((323 : ℝ) / 156) with hεddef
  have hεdpos : 0 < εd := Real.rpow_pos_of_pos (by norm_num) _
  -- the box data carried by `Adm` and `goodSet`
  set av : ℝ := _root_.BoseGases.a v with havdef
  have hav0 : 0 ≤ av := le_of_lt hav
  set κ₀ : ℝ := 16 + 36 * K1s * (R / av) ^ 2 with hκ₀def
  have hκ₀pos : 0 < κ₀ := by
    rw [hκ₀def]; nlinarith [hK1s0, sq_nonneg (R / av)]
  have hκ₀0 : 0 ≤ κ₀ := le_of_lt hκ₀pos
  -- the logarithmic threshold of the `R₂` row
  obtain ⟨δ₁, hδ₁pos, hδ₁val⟩ :=
    Work.BoseFixB1S.fsXp_mul_log_le_one
      (K := 4 * Kc ^ 2 * av / (Real.pi ^ 2 * D * κ₀) + 1) (c := 12.5) (M := 1)
      (by
        have h1 : 0 ≤ 4 * Kc ^ 2 * av / (Real.pi ^ 2 * D * κ₀) :=
          div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Kc)) hav0)
            (le_of_lt (mul_pos (mul_pos (pow_pos Real.pi_pos 2) hDpos) hκ₀pos))
        linarith)
      (by norm_num) (by norm_num)
  refine ⟨min (min ε₁ ε₃) (min δ₁ (min (1 / 2) εd)), κ₀, C₀, ?_,
    hκ₀0, hC₀0, ?_⟩
  · exact lt_min (lt_min hε₁pos hε₃pos) (lt_min hδ₁pos (lt_min (by norm_num) hεdpos))
  intro μ hAdm n Φ u hu hn hΦ hnorm
  -- ### unpacking the admissibility and the regime
  have hμpos : 0 < μ := hAdm.1
  have htε₀ : μ * av ^ 3 ≤ min (min ε₁ ε₃) (min δ₁ (min (1 / 2) εd)) := hAdm.2.1
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hAdm₃ : Work.BoseBoxFix.Adm v ε₃ μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have htδ : μ * av ^ 3 ≤ δ₁ :=
    le_trans htε₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have ht1 : μ * av ^ 3 ≤ 1 / 2 :=
    le_trans htε₀ (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have htεd : μ * av ^ 3 ≤ εd :=
    le_trans htε₀ (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have ht0 : 0 < μ * av ^ 3 := mul_pos hμpos (by positivity)
  have htle1 : μ * av ^ 3 ≤ 1 := by linarith
  obtain ⟨h16R, h16Rd, hdpos, hdle1, hVpos, hVcube, hVside, hmuV⟩ := hreg μ hAdm₁ u hu
  have hℓpos : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hcpos0 : 0 < Work.BoseFixB1.sbCut μ av := Work.BoseFixB1S.sbCut_pos hμpos hav
  -- ### the exponents at FS's parameters
  have hΓeq : Work.BoseFixB1B.PBΓ v μ = Work.BoseBox.fsXp (μ * av ^ 3) (143.5 : ℝ) := by
    have hKB : Work.BoseFixB1B.PBKB v μ = Work.BoseBox.fsXp (μ * av ^ 3) (-6 : ℝ) := rfl
    have h1 : (Work.BoseFixB1B.PBKB v μ) ^ 3 = Work.BoseBox.fsXp (μ * av ^ 3) (-18 : ℝ) := by
      rw [hKB, Work.BoseBox.fsXp_pow (le_of_lt ht0)]
      norm_num
    have h2 : (μ * av ^ 3) ^ (1 / 2 : ℝ) = Work.BoseBox.fsXp (μ * av ^ 3) (161.5 : ℝ) := by
      conv_lhs => rw [Work.BoseBox.delta_eq_fsXp (le_of_lt ht0)]
      rw [Work.BoseBox.fsXp_rpow (le_of_lt ht0)]
      norm_num
    rw [Work.BoseFixB1B.PBΓ, Work.FockBridge.dlGamma, h1, h2,
      Work.BoseBox.fsXp_mul ht0]
    norm_num
  have hΓ0 : 0 ≤ Work.BoseFixB1B.PBΓ v μ := by
    rw [hΓeq]; exact le_of_lt (Work.BoseBox.fsXp_pos ht0)
  have hΓle1 : Work.BoseFixB1B.PBΓ v μ ≤ 1 := by
    rw [hΓeq]; exact Work.BoseBox.fsXp_le_one ht0 htle1 (by norm_num)
  have havc : av * Work.BoseFixB1.sbCut μ av = Work.BoseBox.fsXp (μ * av ^ 3) (156 : ℝ) := by
    have h := Work.BoseFixB1S.sbCut_eq_inv_mul (A := av) (μ := μ) hav hμpos
    have hX : Work.BoseBox.fsXp (μ * av ^ 3) (156 : ℝ) ≠ 0 :=
      ne_of_gt (Work.BoseBox.fsXp_pos (c := (156 : ℝ)) ht0)
    rw [h]
    field_simp
  have hacΓ : av * Work.BoseFixB1.sbCut μ av ≤ Work.BoseFixB1B.PBΓ v μ := by
    rw [havc, hΓeq]
    exact Work.BoseBox.fsXp_le_fsXp ht0 htle1 (by norm_num)
  have hac_half : av * Work.BoseFixB1.sbCut μ av ≤ 1 / 2 := by
    rw [havc]
    exact Work.BoseFixB1.fsXp_le_of_bound (le_of_lt ht0) (by norm_num) (by norm_num)
      (le_trans htεd (le_of_eq hεddef))
  -- the two `R`-ratios
  have hχR0 : R ≤ Work.BoseFixB1.bSide v μ * Submission.BoseGases.chiR0 := by
    have h := (hε₃val μ hμpos (le_trans hAdm.2.1
      (le_trans (min_le_left _ _) (min_le_right _ _)))).2
    rwa [Work.BoseFixGlue.ℓB] at h
  -- ### the two cases
  by_cases hn1 : n ≤ 1
  · -- ## `n = 1`: the pairing word vanishes
    have hA2z : Work.BoseFixB1.bA2 v h μ Φ u = 0 := by
      rw [Work.BoseFixB1.bA2, Work.BoseFixB1.boxA2]
      refine Finset.sum_eq_zero (fun p hp => ?_)
      exfalso
      have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      exact hne (Fin.ext (by omega))
    have hsp0 : 0 ≤ Work.BoseFixB1S.bSpectralCube v μ Φ u := by
      rw [Work.BoseFixB1S.bSpectralCube]
      exact Work.BoseFixB1.tBwordKinInd_nonneg _
    have hχM0 : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
        (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u :=
      Work.SmallBoxSliding.chiMass_nonneg _ _ _ u
    have hI0 : 0 ≤ Work.BoseFixB1.bI v μ Φ := Work.BoseFixB1.bI_nonneg v μ Φ
    have hQ0 : 0 ≤ Work.BoseFixB1.bQ v μ Φ u := Work.BoseFixB1.bQ_nonneg v μ Φ u
    have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h1 : 0 ≤ (1 / 2) * (1 + κ₀ * Work.BoseFixB1B.PBΓ v μ) * Submission.BoseGases.g0w0Mass h
        * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u := by
      have hA : 0 ≤ 1 + κ₀ * Work.BoseFixB1B.PBΓ v μ := by linarith [mul_nonneg hκ₀0 hΓ0]
      have hB : 0 ≤ (((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2 :=
        div_nonneg (mul_nonneg (by linarith) hnR) (by positivity)
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) (le_of_lt hDpos)) hB)
        hχM0
    have h2 : 0 ≤ C₀ * av * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
        * Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
            (Work.BoseFixB1.bV v μ u) Φ := by
      have hc1 : 0 ≤ μ + (n : ℝ) / Work.BoseFixB1.bV v μ u :=
        add_nonneg (le_of_lt hμpos) (div_nonneg hnR (le_of_lt hVpos))
      have hq : 0 ≤ Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u) (Work.BoseFixB1.bV v μ u) Φ := by
        rw [Work.UBBInputs8.cnPlusBoxInd]
        exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
      exact mul_nonneg (mul_nonneg (mul_nonneg hC₀0 hav0) hc1) hq
    have h3 : 0 ≤ C₀ * av * (Work.BoseFixB1.sbCut μ av) ^ 3
        * ((n : ℝ) / Work.BoseFixB1.bV v μ u)
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC₀0 hav0) (by positivity))
        (div_nonneg hnR (le_of_lt hVpos))) hχM0
    rw [hA2z]
    linarith
  · have hn2 : 2 ≤ n := by omega
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.cast_add, Nat.cast_one]
    have hN1 : 1 ≤ N := by omega
    -- ### the box vocabulary
    set ℓ : ℝ := Work.BoseFixB1.bSide v μ with hℓdef
    set dd : ℝ := Work.BoseFixB1.bD v μ with hddef
    set V : ℝ := Work.BoseFixB1.bV v μ u with hVdef
    set A : Set E3 := Work.BoseFixB1.bA v μ u with hAdef
    set Mv : ℕ := Work.BoseFixB1.bM v μ with hMvdef
    set χ : E3 → ℝ := Submission.BoseGases.chiSmallB Mv ℓ dd u with hχdef
    set 𝒲 : E3 → ℝ := Work.BoseFixB1B.wSmallInner Mv ℓ dd (Submission.BoseGases.g0 v h) with h𝒲def
    set c : ℝ := Work.BoseFixB1.sbCut μ av with hcdef
    set Xw : ℝ := ∫ z : E3, (χ z) ^ 2 with hXwdef
    have hℓpos' : 0 < ℓ := hℓpos
    have hcpos : 0 < c := hcpos0
    have hMv48 : Mv = Work.BoseBox.mValue := by rw [hMvdef]; rfl
    have hMv1 : 1 ≤ Mv := by rw [hMv48]; norm_num [Work.BoseBox.mValue]
    have hMv3 : 3 ≤ Mv := by rw [hMv48]; norm_num [Work.BoseBox.mValue]
    have hMv5 : 5 ≤ Mv := by rw [hMv48]; norm_num [Work.BoseBox.mValue]
    have hAmeas : MeasurableSet A := by
      show MeasurableSet (Submission.BoseGases.dlBox ℓ dd u)
      exact Work.SmallBoxSliding.measurableSet_dlBox ℓ dd u
    have hAsub : A ⊆ Submission.BoseGases.acube ℓ := by
      show Submission.BoseGases.dlBox ℓ dd u ⊆ Submission.BoseGases.acube ℓ
      exact Work.SmallBoxSliding.dlBox_subset_acube ℓ dd u
    have hAvol : V = (MeasureTheory.volume A).toReal := by
      show Work.SmallBoxSliding.boxMass ℓ dd u
          = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ dd u)).toReal
      exact Work.SmallBoxSliding.boxMass_eq_measureReal ℓ dd u
    have hχc2 : ContDiff ℝ 2 χ := by
      show ContDiff ℝ 2 (Submission.BoseGases.chiSmallB Mv ℓ dd u)
      exact Work.BoseFixB1.chiSmallB_contDiff_two hMv3 u
    have hχs : HasCompactSupport χ := by
      show HasCompactSupport (Submission.BoseGases.chiSmallB Mv ℓ dd u)
      exact Submission.BoseGases.chiSmallB_hasCompactSupport hMv1 hℓpos' u
    have hχsupp : ∀ z, z ∉ A → χ z = 0 := by
      intro z hz
      show Submission.BoseGases.chiSmallB Mv ℓ dd u z = 0
      exact Work.BoseFixB1S.chiSmallB_eq_zero_of_notMem_dlBox hMv1 hℓpos' hdpos u hz
    have hχnn : ∀ z, 0 ≤ χ z := fun z => by
      show 0 ≤ Submission.BoseGases.chiSmallB Mv ℓ dd u z
      exact Submission.BoseGases.chiSmallB_nonneg Mv ℓ dd u z
    have hκχb : ∀ z, |χ z| ≤ κχ := by
      intro z
      show |Submission.BoseGases.chiSmallB Mv ℓ dd u z|
          ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue
      have h1 := Work.SmallBoxSliding.abs_chiSmallB_le (M := Mv) (ℓ := ℓ) (d := dd) hMv1 u z
      have h2 : Submission.BoseGases.chiSmall Mv ((ℓ * dd)⁻¹ • z - u)
          ≤ Submission.BoseGases.chiSmallDecay Mv := by
        have h3 := Submission.BoseGases.chiSmall_decay_coord_le_decay hMv1 ((ℓ * dd)⁻¹ • z - u)
        rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg Mv _)] at h3
      rw [hMv48]
      calc |Submission.BoseGases.chiSmallB Mv ℓ dd u z|
          ≤ Submission.BoseGases.chiSupAbs
              * Submission.BoseGases.chiSmall Mv ((ℓ * dd)⁻¹ • z - u) := h1
        _ ≤ Submission.BoseGases.chiSupAbs
              * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue :=
            mul_le_mul_of_nonneg_left h2 Submission.BoseGases.chiSupAbs_nonneg
    -- ### the kernel data
    have h16Rℓ : 16 * R ≤ ℓ := h16R
    have h16Rℓd : 16 * R ≤ ℓ * dd := h16Rd
    have hVpos' : 0 < V := hVpos
    obtain ⟨hsup0, hfin0, _hM10⟩ := hKcbound (ℓ := ℓ) (d := dd) hℓpos' hdpos h16Rℓ h16Rℓd
    have h𝒲int : MeasureTheory.Integrable 𝒲 := by
      rw [h𝒲def]
      exact Work.BoseFixB1S.wSmallInner_integrable16 h hR hv hv1 hvrad hv_supp
        (le_trans (by norm_num) hMv5) hℓpos' hdpos h16Rℓ h16Rℓd
    have hsup : ∀ q : E3, |Submission.BoseGases.pairW 𝒲 q| ≤ Kc * av := by
      intro q
      rw [h𝒲def]
      exact hsup0 q
    have hfin : MeasureTheory.Integrable (fun q : E3 =>
        Submission.BoseGases.pairW 𝒲 q ^ 2 / ‖q‖ ^ 2) := by
      rw [h𝒲def]; exact hfin0
    -- the sharp Newtonian mass at the window
    have hJ0 : ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
        Submission.BoseGases.pairW 𝒲 q ^ 2 / ‖q‖ ^ 2)
        ≤ 2 * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2)) * D := by
      rw [h𝒲def, hDdef]
      exact hK1sh (ℓ := ℓ) (d := dd) hℓpos' hdpos (by linarith [h16Rℓd]) hχR0
    -- ### the two integrability inputs of the chain
    have hBle : ∀ q : E3, |Submission.BoseGases.pairW 𝒲 q / V|
        ≤ 1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
          + 2 * Ks * av / V := by
      intro q
      have h := Work.BoseFixB1B.pairRung.hBle_of (n := N + 1) (V := V) (Ks := Ks)
        (av := av) (c := c) (K := Kc) (𝒲 := 𝒲) hVpos' hav0 hKsKc hsup q
      have hcast : (1 : ℝ) / (((N + 1 : ℕ) : ℝ) + 1) = 1 / ((N : ℝ) + 2) := by
        rw [Nat.cast_add, Nat.cast_one]; congr 1; ring
      rw [hcast] at h
      exact h
    have hIntK : MeasureTheory.Integrable (fun q : E3 =>
        (Submission.BoseGases.pairW 𝒲 q / V) ^ 2 /
          (1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
            + 2 * Ks * av / V)) := by
      have hh := Work.BoseFixB1B.pairRung.hIntK_of (n := N + 1) (V := V) (Ks := Ks)
        (av := av) (c := c) (𝒲 := 𝒲) hVpos' hKs0 (by linarith) (le_of_lt hcpos) h𝒲int hfin
      simpa only [Nat.cast_add, Nat.cast_one] using hh
    have hIntQ : MeasureTheory.Integrable (fun q : E3 =>
        (1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
          + 2 * Ks * av / V
          - Real.sqrt ((1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
              + 2 * Ks * av / V) ^ 2
            - (Submission.BoseGases.pairW 𝒲 q / V) ^ 2)) / 2) := by
      have hh := Work.BoseFixB1B.pairRung.hIntK_of (n := N + 1) (V := V) (Ks := Ks)
        (av := av) (c := c) (𝒲 := 𝒲) hVpos' hKs0 (by linarith) (le_of_lt hcpos) h𝒲int hfin
      have hIK : MeasureTheory.Integrable (fun q : E3 =>
          (Submission.BoseGases.pairW 𝒲 q / V) ^ 2 /
            (1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
              + 2 * Ks * av / V)) := by
        refine hh.congr (Filter.Eventually.of_forall fun q => ?_)
        have hcast : (1 : ℝ) / (((N + 1 : ℕ) : ℝ) + 1) = 1 / ((N : ℝ) + 2) := by
          rw [Nat.cast_add, Nat.cast_one]; congr 1; ring
        rw [hcast]
      exact Work.BoseFixB1B.intQ_of_intK (N := N) (V := V) (Ks := Ks) (av := av) (c := c)
        (𝒲 := 𝒲) hVpos' hKs0 (by linarith) hBle hIK
    have hintP : MeasureTheory.Integrable (fun q : E3 =>
        (1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
            + 2 * Ks * av / V) *
          Work.BoseFixB1.boxWinModePGen ℓ V A χ Φ q) := by
      have hfsK : MeasureTheory.Integrable (fun q : E3 =>
          Submission.BoseGases.fsKinCoeff c ‖q‖ *
            Work.BoseFixB1.boxWinModePGen ℓ V A χ Φ q) :=
        Work.BoseFixB1S.win.chiSmallB_fsKinPGenIntegrable (n := N + 1) (ℓ := ℓ) (d := dd)
          hℓpos' hdpos hdle1 hMv5 u hVpos' hcpos hΦ
      have hP : MeasureTheory.Integrable (fun q : E3 =>
          Work.BoseFixB1.boxWinModePGen ℓ V A χ Φ q) :=
        (Work.BoseFixB1S.win.chiSmallB_windowIntegrable (n := N + 1) (ℓ := ℓ) (d := dd)
          hℓpos' hdpos hdle1 hMv5 u hVpos' hΦ).1
      have h1 := hfsK.const_mul (1 / ((N : ℝ) + 1 + 1))
      have h2 := hP.const_mul (2 * Ks * av / V)
      refine (h1.add h2).congr (Filter.Eventually.of_forall fun q => ?_)
      simp only [Pi.add_apply]
      ring
    have hintR : MeasureTheory.Integrable (fun q : E3 =>
        (1 / V) * Submission.BoseGases.pairW 𝒲 q *
          Work.BoseFixB1.boxWinModeRGen ℓ V A χ Φ q) := by
      have hh : MeasureTheory.Integrable (fun q : E3 =>
          Submission.BoseGases.pairW 𝒲 q * Work.BoseFixB1.boxWinModeRGen ℓ V A χ Φ q) :=
        Work.BoseFixB1B.pairRung.winModeRGenMulPairWIntegrable (n := N + 1) (a := ℓ) (volA := V)
          hℓpos' hVpos' hAmeas hAsub hAvol hχc2 hχs hχsupp (fun z => hκχb z) h𝒲int hΦ
      have h2 : (fun q : E3 => (1 / V) * (Submission.BoseGases.pairW 𝒲 q
            * Work.BoseFixB1.boxWinModeRGen ℓ V A χ Φ q))
          = fun q : E3 => (1 / V) * Submission.BoseGases.pairW 𝒲 q
            * Work.BoseFixB1.boxWinModeRGen ℓ V A χ Φ q := by
        funext q; ring
      rw [← h2]
      exact hh.const_mul (1 / V)
    -- ### the three-row bracket (`sharpTerm1BoundRefined3`) is the chain's `hI`
    have hnorm' : (∫ x in Submission.BoseGases.abox (N + 1) ℓ, (Φ x) ^ 2) = 1 := hnorm
    have hI : ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
          (1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / V
            - Real.sqrt ((1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
                + 2 * Ks * av / V) ^ 2
              - (Submission.BoseGases.pairW 𝒲 q / V) ^ 2)) / 2
        ≤ (1 + 8 * (av * c)) * (((N : ℝ) + 2) / (4 * V ^ 2))
            * (((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
                (Submission.BoseGases.pairW 𝒲 q) ^ 2 / ‖q‖ ^ 2))
          + (1 / Real.pi ^ 2) * (((N : ℝ) + 2) * c * Kc ^ 2 * av ^ 2 / V ^ 2)
              * (1 + Real.log ((av * c)⁻¹))
          + (1 / (3 * Real.pi ^ 2)) * (Kc ^ 2 * av * c ^ 3 / (Ks * V)) :=
      Work.BoseB1Cube.sharpTerm1BoundRefined3 (N := N) (V := V) (c := c) (Kc := Kc) (Ks := Ks)
        (av := av) (g := Submission.BoseGases.pairW 𝒲)
        hVpos' hcpos hKs0 (by linarith) hKc0 hKsKc hac_half hsup hfin hIntQ
    -- ### the sharp chain
    have hchain := Work.BoseB1Cube.chainA2SharpRefined3 (N := N) hN1 (ℓ := ℓ) (volA := V)
      (c := c) (Kc := Kc) (Ks := Ks) (av := av) (κ := κχ) (μ := μ)
      (Ac := A) (χ := χ) (𝒲 := 𝒲) (Ψ := Φ)
      hℓpos' hVpos' hKs0 (by linarith) hcpos hKc0 hKsKc (le_of_lt hμpos) hAmeas hAsub hAvol
      hχc2 hχs hχsupp hχnn hκχb hΦ hnorm' h𝒲int hsup hfin hintP hintR hIntK hIntQ hI
    -- ### the row arithmetic
    have hXw0 : 0 ≤ Xw := by rw [hXwdef]; exact integral_nonneg (fun z => sq_nonneg _)
    have hSle : Work.BoseFixB1S.boxFlatCount V ℓ A Φ ≤ (N : ℝ) + 1 := by
      have hh := Work.BoseFixB1S.boxFlatCount_le_NB1 (N := N + 1) hℓpos' hVpos' hAmeas hAsub
        hAvol hΦ.continuous
      rw [hnorm', mul_one] at hh
      simpa only [Nat.cast_add, Nat.cast_one] using hh
    have hS0 : 0 ≤ Work.BoseFixB1S.boxFlatCount V ℓ A Φ := by
      rw [Work.BoseFixB1S.boxFlatCount]
      exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
    have hJ00 : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
        Submission.BoseGases.pairW 𝒲 q ^ 2 / ‖q‖ ^ 2) :=
      mul_nonneg (by positivity) (integral_nonneg (fun q => div_nonneg (sq_nonneg _) (sq_nonneg _)))
    have hnp0 : 0 ≤ Work.UBBInputs8.cnPlusBoxInd ℓ A V Φ := by
      rw [Work.UBBInputs8.cnPlusBoxInd]
      exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
    have hμn : 0 ≤ μ + ((N : ℝ) + 1) / V :=
      add_nonneg (le_of_lt hμpos) (div_nonneg (by positivity) (le_of_lt hVpos'))
    -- ### the gates
    have hΓ' : Work.BoseFixB1B.PBΓ v μ = Work.BoseBox.fsXp (μ * av ^ 3) (143.5 : ℝ) := hΓeq
    have hcav : av * c = Work.BoseBox.fsXp (μ * av ^ 3) (156 : ℝ) := by
      rw [hcdef]; exact havc
    have hL0 : 0 ≤ 1 + Real.log ((av * c)⁻¹) := by
      have h2 : Work.BoseBox.fsXp (μ * av ^ 3) (156 : ℝ) ≤ 1 / 2 := by
        rw [← hcav]; exact hac_half
      have h3 : (0 : ℝ) < Work.BoseBox.fsXp (μ * av ^ 3) (156 : ℝ) :=
        Work.BoseBox.fsXp_pos (c := (156 : ℝ)) ht0
      have h4 : 1 ≤ (Work.BoseBox.fsXp (μ * av ^ 3) (156 : ℝ))⁻¹ :=
        (one_le_inv₀ h3).mpr (le_trans h2 (by norm_num))
      have h5 : 0 ≤ Real.log ((Work.BoseBox.fsXp (μ * av ^ 3) (156 : ℝ))⁻¹) :=
        Real.log_nonneg h4
      rw [hcav]
      linarith
    have hceil : 1 + Real.log ((av * c)⁻¹) ≤ 1 + |Real.log (μ * av ^ 3)| := by
      have h2 : (av * c)⁻¹ = (μ * av ^ 3) ^ ((-156 : ℝ) / 323) := by
        rw [hcav, Work.BoseBox.fsXp_inv (c := 156) ht0]
        rfl
      have h3 : Real.log ((av * c)⁻¹) = ((-156 : ℝ) / 323) * Real.log (μ * av ^ 3) := by
        rw [h2, Real.log_rpow ht0]
      have h4 : Real.log (μ * av ^ 3) ≤ 0 := Real.log_nonpos (le_of_lt ht0) htle1
      rw [h3]
      have h5 : ((-156 : ℝ) / 323) * Real.log (μ * av ^ 3) ≤ -Real.log (μ * av ^ 3) := by
        nlinarith [h4]
      have h6 : -Real.log (μ * av ^ 3) ≤ |Real.log (μ * av ^ 3)| := neg_le_abs _
      linarith
    -- the `R`-ratios
    have hside : ℓ = av * Work.BoseBox.fsXp (μ * av ^ 3) (-163 : ℝ) := by
      rw [hℓdef, Work.BoseFixB1.bSide]
      exact Work.BoseFixB1.sideAt_eq_fsXp hav hμpos
    have hdd : ℓ * dd = av * Work.BoseBox.fsXp (μ * av ^ 3) (-157 : ℝ) := by
      rw [hℓdef, hddef, Work.BoseFixB1.bSide, Work.BoseFixB1.bD, mul_comm]
      exact Work.BoseFixB1.d_mul_sideAt_eq hav hμpos
    have hRsq1 : (R / ℓ) ^ 2 ≤ (R / av) ^ 2 * Work.BoseFixB1B.PBΓ v μ := by
      rw [hside, hΓeq]
      have hEq : R / (av * Work.BoseBox.fsXp (μ * av ^ 3) (-163 : ℝ))
          = (R / av) * Work.BoseBox.fsXp (μ * av ^ 3) (163 : ℝ) := by
        rw [← Work.BoseBox.fsXp_inv (t := μ * av ^ 3) (c := 163) ht0]
        field_simp
      rw [hEq, mul_pow]
      have hXsq : (Work.BoseBox.fsXp (μ * av ^ 3) (163 : ℝ)) ^ 2
          = Work.BoseBox.fsXp (μ * av ^ 3) (326 : ℝ) := by
        rw [Work.BoseBox.fsXp_pow (le_of_lt ht0)]; norm_num
      rw [hXsq]
      have hsplit326 : Work.BoseBox.fsXp (μ * av ^ 3) (326 : ℝ)
          = Work.BoseBox.fsXp (μ * av ^ 3) (182.5 : ℝ)
            * Work.BoseBox.fsXp (μ * av ^ 3) (143.5 : ℝ) := by
        rw [Work.BoseBox.fsXp_mul ht0]; norm_num
      rw [hsplit326]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg (R / av))
      exact mul_le_of_le_one_left
        (le_of_lt (Work.BoseBox.fsXp_pos (c := (143.5 : ℝ)) ht0))
        (Work.BoseBox.fsXp_le_one ht0 htle1 (by norm_num))
    have hRsq2 : (R / (ℓ * dd)) ^ 2 ≤ (R / av) ^ 2 * Work.BoseFixB1B.PBΓ v μ := by
      rw [hdd, hΓeq]
      have hEq : R / (av * Work.BoseBox.fsXp (μ * av ^ 3) (-157 : ℝ))
          = (R / av) * Work.BoseBox.fsXp (μ * av ^ 3) (157 : ℝ) := by
        rw [← Work.BoseBox.fsXp_inv (t := μ * av ^ 3) (c := 157) ht0]
        field_simp
      rw [hEq, mul_pow]
      have hXsq : (Work.BoseBox.fsXp (μ * av ^ 3) (157 : ℝ)) ^ 2
          = Work.BoseBox.fsXp (μ * av ^ 3) (314 : ℝ) := by
        rw [Work.BoseBox.fsXp_pow (le_of_lt ht0)]; norm_num
      rw [hXsq]
      have hsplit314 : Work.BoseBox.fsXp (μ * av ^ 3) (314 : ℝ)
          = Work.BoseBox.fsXp (μ * av ^ 3) (170.5 : ℝ)
            * Work.BoseBox.fsXp (μ * av ^ 3) (143.5 : ℝ) := by
        rw [Work.BoseBox.fsXp_mul ht0]; norm_num
      rw [hsplit314]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg (R / av))
      exact mul_le_of_le_one_left
        (le_of_lt (Work.BoseBox.fsXp_pos (c := (143.5 : ℝ)) ht0))
        (Work.BoseBox.fsXp_le_one ht0 htle1 (by norm_num))
    have hdelta : (R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2
        ≤ 2 * (R / av) ^ 2 * Work.BoseFixB1B.PBΓ v μ := by linarith
    -- the `hgate` of the row arithmetic
    have hgate : (1 + 8 * (av * c)) * (2 * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2)))
        + 4 * c * Kc ^ 2 * av ^ 2 * (1 + Real.log ((av * c)⁻¹)) / (Real.pi ^ 2 * D)
        ≤ 2 * (1 + κ₀ * Work.BoseFixB1B.PBΓ v μ) := by
      have hδ'0 : 0 ≤ (R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2 := by positivity
      have hJ1b : 2 * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2))
          ≤ 2 + 4 * K1s * (R / av) ^ 2 * Work.BoseFixB1B.PBΓ v μ := by
        have h := mul_le_mul_of_nonneg_left hdelta hK1s0
        nlinarith [h, hK1s0, hΓ0, sq_nonneg (R / av)]
      have hpart1 : (1 + 8 * (av * c)) * (2 * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2)))
          ≤ 2 + κ₀ * Work.BoseFixB1B.PBΓ v μ := by
        have h8 : 1 + 8 * (av * c) ≤ 1 + 8 * Work.BoseFixB1B.PBΓ v μ := by linarith
        have hΓ2 : Work.BoseFixB1B.PBΓ v μ * Work.BoseFixB1B.PBΓ v μ
            ≤ Work.BoseFixB1B.PBΓ v μ := by nlinarith [hΓ0, hΓle1]
        have hnn : 0 ≤ 2 * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2)) :=
          mul_nonneg (by norm_num) (by linarith [mul_nonneg hK1s0 hδ'0])
        have hb0 : 0 ≤ 1 + 8 * Work.BoseFixB1B.PBΓ v μ := by linarith
        have hstep := mul_le_mul h8 hJ1b hnn hb0
        have hexp : (1 + 8 * Work.BoseFixB1B.PBΓ v μ)
            * (2 + 4 * K1s * (R / av) ^ 2 * Work.BoseFixB1B.PBΓ v μ)
            = 2 + 16 * Work.BoseFixB1B.PBΓ v μ
              + 4 * K1s * (R / av) ^ 2 * Work.BoseFixB1B.PBΓ v μ
              + 32 * K1s * (R / av) ^ 2 * (Work.BoseFixB1B.PBΓ v μ
                  * Work.BoseFixB1B.PBΓ v μ) := by ring
        have h32 : 32 * K1s * (R / av) ^ 2 * (Work.BoseFixB1B.PBΓ v μ
            * Work.BoseFixB1B.PBΓ v μ)
            ≤ 32 * K1s * (R / av) ^ 2 * Work.BoseFixB1B.PBΓ v μ := by
          refine mul_le_mul_of_nonneg_left hΓ2 ?_
          positivity
        rw [hκ₀def]
        linarith [hstep, hexp.le, hexp.ge, h32]
      have hpart2 : 4 * c * Kc ^ 2 * av ^ 2 * (1 + Real.log ((av * c)⁻¹)) / (Real.pi ^ 2 * D)
          ≤ κ₀ * Work.BoseFixB1B.PBΓ v μ := by
        rw [hΓeq]
        have hsplit : Work.BoseBox.fsXp (μ * av ^ 3) (156 : ℝ)
            = Work.BoseBox.fsXp (μ * av ^ 3) (12.5 : ℝ)
              * Work.BoseBox.fsXp (μ * av ^ 3) (143.5 : ℝ) := by
          rw [Work.BoseBox.fsXp_mul ht0]; norm_num
        have hprod : av * c = Work.BoseBox.fsXp (μ * av ^ 3) (12.5 : ℝ)
            * Work.BoseBox.fsXp (μ * av ^ 3) (143.5 : ℝ) := by rw [hcav, hsplit]
        have hX125 : 0 < Work.BoseBox.fsXp (μ * av ^ 3) (12.5 : ℝ) :=
          Work.BoseBox.fsXp_pos (c := (12.5 : ℝ)) ht0
        have hX143 : 0 < Work.BoseBox.fsXp (μ * av ^ 3) (143.5 : ℝ) :=
          Work.BoseBox.fsXp_pos (c := (143.5 : ℝ)) ht0
        have hthr : 4 * Kc ^ 2 * av * Work.BoseBox.fsXp (μ * av ^ 3) (12.5 : ℝ)
            * (1 + |Real.log (μ * av ^ 3)|) / (Real.pi ^ 2 * D) ≤ κ₀ := by
          have h := hδ₁val (μ * av ^ 3) ht0 htδ
          rw [Real.rpow_one] at h
          have hZ0 : 0 ≤ Work.BoseBox.fsXp (μ * av ^ 3) (12.5 : ℝ)
              * (1 + |Real.log (μ * av ^ 3)|) :=
            mul_nonneg (le_of_lt hX125) (by positivity)
          have h2 : (4 * Kc ^ 2 * av / (Real.pi ^ 2 * D * κ₀) + 1)
              * (Work.BoseBox.fsXp (μ * av ^ 3) (12.5 : ℝ)
                * (1 + |Real.log (μ * av ^ 3)|)) ≤ 1 := by
            have hEq : (4 * Kc ^ 2 * av / (Real.pi ^ 2 * D * κ₀) + 1)
                * (Work.BoseBox.fsXp (μ * av ^ 3) (12.5 : ℝ)
                  * (1 + |Real.log (μ * av ^ 3)|))
                = (4 * Kc ^ 2 * av / (Real.pi ^ 2 * D * κ₀) + 1)
                  * Work.BoseBox.fsXp (μ * av ^ 3) (12.5 : ℝ)
                  * (1 + |Real.log (μ * av ^ 3)|) := by ring
            rw [hEq]
            exact h
          have h3 : (4 * Kc ^ 2 * av / (Real.pi ^ 2 * D * κ₀))
              * (Work.BoseBox.fsXp (μ * av ^ 3) (12.5 : ℝ)
                * (1 + |Real.log (μ * av ^ 3)|)) ≤ 1 := by
            have h4 := mul_le_mul_of_nonneg_right
              (show 4 * Kc ^ 2 * av / (Real.pi ^ 2 * D * κ₀)
                ≤ 4 * Kc ^ 2 * av / (Real.pi ^ 2 * D * κ₀) + 1 by linarith) hZ0
            linarith [h4, h2]
          have h5 := mul_le_mul_of_nonneg_right h3 (le_of_lt hκ₀pos)
          have heq : κ₀ * ((4 * Kc ^ 2 * av / (Real.pi ^ 2 * D * κ₀))
                * (Work.BoseBox.fsXp (μ * av ^ 3) (12.5 : ℝ)
                  * (1 + |Real.log (μ * av ^ 3)|)))
              = 4 * Kc ^ 2 * av * Work.BoseBox.fsXp (μ * av ^ 3) (12.5 : ℝ)
                * (1 + |Real.log (μ * av ^ 3)|) / (Real.pi ^ 2 * D) := by
            field_simp
          linarith [h5, heq.le, heq.ge]
        have hLle : 1 + Real.log ((av * c)⁻¹) ≤ 1 + |Real.log (μ * av ^ 3)| := hceil
        have hpiv : 4 * c * Kc ^ 2 * av ^ 2 = 4 * Kc ^ 2 * av
            * (Work.BoseBox.fsXp (μ * av ^ 3) (12.5 : ℝ)
              * Work.BoseBox.fsXp (μ * av ^ 3) (143.5 : ℝ)) := by
          rw [← hprod]; ring
        have hstep1 : 4 * c * Kc ^ 2 * av ^ 2 * (1 + Real.log ((av * c)⁻¹)) / (Real.pi ^ 2 * D)
            ≤ 4 * Kc ^ 2 * av * (Work.BoseBox.fsXp (μ * av ^ 3) (12.5 : ℝ)
                * Work.BoseBox.fsXp (μ * av ^ 3) (143.5 : ℝ))
              * (1 + |Real.log (μ * av ^ 3)|) / (Real.pi ^ 2 * D) := by
          rw [hpiv]
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left hLle ?_
          exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Kc)) hav0)
            (mul_nonneg (le_of_lt hX125) (le_of_lt hX143))
        refine le_trans hstep1 ?_
        have heq2 : 4 * Kc ^ 2 * av * (Work.BoseBox.fsXp (μ * av ^ 3) (12.5 : ℝ)
                * Work.BoseBox.fsXp (μ * av ^ 3) (143.5 : ℝ))
              * (1 + |Real.log (μ * av ^ 3)|) / (Real.pi ^ 2 * D)
            = (4 * Kc ^ 2 * av * Work.BoseBox.fsXp (μ * av ^ 3) (12.5 : ℝ)
                * (1 + |Real.log (μ * av ^ 3)|) / (Real.pi ^ 2 * D))
              * Work.BoseBox.fsXp (μ * av ^ 3) (143.5 : ℝ) := by ring
        rw [heq2]
        exact mul_le_mul_of_nonneg_right hthr (le_of_lt hX143)
      linarith [hpart1, hpart2]
    -- ### the row arithmetic
    have harith := r3RowArith (S := Work.BoseFixB1S.boxFlatCount V ℓ A Φ) (X := Xw) (V := V)
      (D := D) (Kc := Kc) (Ks := Ks) (c := c) (av := av) (κ := κ₀)
      (Γ := Work.BoseFixB1B.PBΓ v μ) (C := C₀) (κχ := κχ)
      (J0 := ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, Submission.BoseGases.pairW 𝒲 q ^ 2 / ‖q‖ ^ 2))
      (J1 := 2 * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2)))
      (n := (N : ℝ) + 1) (np := Work.UBBInputs8.cnPlusBoxInd ℓ A V Φ)
      hXw0 hVpos' hDpos hSle (by positivity) hKs0 hcpos hav0 hκ₀0 hΓ0 hKc0 hκχ0 hC₀0
      hnp0 hμn hJ00 hJ0 hL0 hgate hC₀C3 hC₀C4
    -- ### rewriting the goal into the chain's vocabulary
    have hscSpec : Work.BoseFixB1S.bSpectralCube v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) u
        = Work.UBBInputs8.tBwordKinInd ℓ A V χ c Φ := rfl
    have hQeq : Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) u
        = Work.UBBInputs8.cnPlusBoxInd ℓ A V Φ := rfl
    have hA2Bunf : Work.BoseFixB1.bA2 v h μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) u
        = Work.BoseFixB1.boxA2 ℓ V A (fun x y => χ x * χ y * 𝒲 (x - y)) Φ := by
      show Work.BoseFixB1.boxA2 ℓ V A (Submission.BoseGases.wSmall1Pair h Mv ℓ dd u) Φ = _
      rw [Work.BoseFixB1B.pairRung.wSmall1Pair_kernel h Mv ℓ dd u]
      rfl
    have hchiM : Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u = Xw := by
      show (∫ z : E3, (Submission.BoseGases.chiSmallB Mv ℓ dd u z) ^ 2) = Xw
      rw [hXwdef]
    have hcast2 : (N : ℝ) + 2 = (N : ℝ) + 1 + 1 := by ring
    rw [hcast2] at hchain
    rw [hscSpec, hA2Bunf, hchiM]
    linarith [hchain, harith]

end Work.BoseB1Cube
