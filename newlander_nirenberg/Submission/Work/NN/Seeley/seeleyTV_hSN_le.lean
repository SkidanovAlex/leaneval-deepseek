import Mathlib
import Submission.Work.NN.Seeley.Setup
import Submission.Work.NN.Seeley.ProdBounds
import Submission.Work.NN.Seeley.Glob
import Submission.Work.NN.Seeley.gSN_cutoff_le
import Submission.Work.NN.Seeley.gSN_bilinear_le
import Submission.Work.NN.Seeley.gDN_bilinear_le

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

set_option linter.unusedSectionVars false

namespace Work.NN.Seeley

open Work.NN.Final

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Germ invariance of the global derivative norms -/

/-- The global iterated derivative depends only on the germ at the point. -/
lemma iteratedFDeriv_eq_of_eventuallyEq {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] {f f' : Y → A} {x : Y}
    (h : f =ᶠ[𝓝 x] f') (i : ℕ) :
    iteratedFDeriv ℝ i f x = iteratedFDeriv ℝ i f' x := by
  rw [← iteratedFDerivWithin_univ, ← iteratedFDerivWithin_univ]
  exact Filter.EventuallyEq.iteratedFDerivWithin_eq (by rwa [nhdsWithin_univ]) h.self_of_nhds i

/-- `gDN` depends only on the germ at each point of the set. -/
lemma gDN_eq_of_eventuallyEq {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] {f f' : Y → A} {Ω : Set Y}
    (h : ∀ x ∈ Ω, f =ᶠ[𝓝 x] f') (i : ℕ) :
    gDN i f Ω = gDN i f' Ω := by
  unfold gDN
  refine le_antisymm (iSup₂_le fun x hx => ?_) (iSup₂_le fun x hx => ?_)
  · rw [iteratedFDeriv_eq_of_eventuallyEq (h x hx) i]
    exact le_iSup₂_of_le x hx le_rfl
  · rw [← iteratedFDeriv_eq_of_eventuallyEq (h x hx) i]
    exact le_iSup₂_of_le x hx le_rfl

/-- `gSN` depends only on the germ at each point of the set. -/
lemma gSN_eq_of_eventuallyEq {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] {f f' : Y → A} {Ω : Set Y}
    (h : ∀ x ∈ Ω, f =ᶠ[𝓝 x] f') (i : ℕ) (α : ℝ) :
    gSN i α f Ω = gSN i α f' Ω := by
  unfold gSN
  refine le_antisymm
      (iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_)
      (iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_)
  · rw [iteratedFDeriv_eq_of_eventuallyEq (h x hx) i,
        iteratedFDeriv_eq_of_eventuallyEq (h y hy) i]
    exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))
  · rw [← iteratedFDeriv_eq_of_eventuallyEq (h x hx) i,
        ← iteratedFDeriv_eq_of_eventuallyEq (h y hy) i]
    exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))

/-! ## The shear composed with `seeleyV` -/

/-- Sup-norm bound for the shear composed with `seeleyV δ g`, over the open lower slab. -/
lemma gDN_seeleyV_shear_le {δ : ℝ} (hδ : 0 < δ) {g : X × ℝ → ℂ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) g {p : X × ℝ | -δ < p.2})
    {c : ℝ} (hc : 1 ≤ c) (k : ℕ) :
    gDN k (fun p : X × ℝ => seeleyV δ g (p.1, -c * p.2))
        {p : X × ℝ | -δ < p.2 ∧ p.2 < 0}
      ≤ ENNReal.ofReal (c ^ k) * gDN k g {p : X × ℝ | 0 < p.2} := by
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  have hv : ContDiff ℝ ∞ (seeleyV δ g) := seeleyV_contDiff hδ hg
  have hcomp := gDN_comp_prod_snd_le (c := -c) (i := k) (u := seeleyV δ g)
      (hv.of_le (by simp)) (Ω := {p : X × ℝ | -δ < p.2 ∧ p.2 < 0})
  have hmax : (max 1 |(-c)|) = c := by
    rw [abs_neg, abs_of_nonneg hcpos.le, max_eq_right hc]
  rw [hmax] at hcomp
  refine hcomp.trans ?_
  have hsub : (fun p : X × ℝ => (p.1, -c * p.2)) '' {p : X × ℝ | -δ < p.2 ∧ p.2 < 0}
      ⊆ {p : X × ℝ | 0 < p.2} := by
    rintro x ⟨p, hp, rfl⟩
    show 0 < -c * p.2
    nlinarith [hcpos, hp.2]
  have hev : ∀ x ∈ (fun p : X × ℝ => (p.1, -c * p.2)) '' {p : X × ℝ | -δ < p.2 ∧ p.2 < 0},
      seeleyV δ g =ᶠ[𝓝 x] g := by
    rintro x ⟨p, hp, rfl⟩
    have hmem : {q : X × ℝ | -(δ / 2) < q.2} ∈ 𝓝 ((p.1, -c * p.2) : X × ℝ) :=
      (isOpen_lt continuous_const continuous_snd).mem_nhds (by
        show -(δ / 2) < -c * p.2
        nlinarith [hδ, hcpos, hp.2])
    filter_upwards [hmem] with q hq
    exact seeleyV_eq δ g (hδ := hδ) (le_of_lt hq)
  refine mul_le_mul' le_rfl ?_
  calc gDN k (seeleyV δ g)
          ((fun p : X × ℝ => (p.1, -c * p.2)) '' {p : X × ℝ | -δ < p.2 ∧ p.2 < 0})
      = gDN k g ((fun p : X × ℝ => (p.1, -c * p.2)) '' {p : X × ℝ | -δ < p.2 ∧ p.2 < 0}) :=
        gDN_eq_of_eventuallyEq hev k
    _ ≤ gDN k g {p : X × ℝ | 0 < p.2} := gDN_mono hsub k g

/-- Hölder-seminorm bound for the shear composed with `seeleyV δ g`, over the open lower slab. -/
lemma gSN_seeleyV_shear_le {δ : ℝ} (hδ : 0 < δ) {g : X × ℝ → ℂ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) g {p : X × ℝ | -δ < p.2})
    {c : ℝ} (hc : 1 ≤ c) (k : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    gSN k α (fun p : X × ℝ => seeleyV δ g (p.1, -c * p.2))
        {p : X × ℝ | -δ < p.2 ∧ p.2 < 0}
      ≤ ENNReal.ofReal (c ^ ((k : ℝ) + α)) * gSN k α g {p : X × ℝ | 0 < p.2} := by
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  have hv : ContDiff ℝ ∞ (seeleyV δ g) := seeleyV_contDiff hδ hg
  have hcomp := gSN_comp_prod_snd_le (c := -c) (i := k) (α := α) hα (u := seeleyV δ g)
      (hv.of_le (by simp)) (Ω := {p : X × ℝ | -δ < p.2 ∧ p.2 < 0})
  have hmax : (max 1 |(-c)|) = c := by
    rw [abs_neg, abs_of_nonneg hcpos.le, max_eq_right hc]
  rw [hmax] at hcomp
  refine hcomp.trans ?_
  have hsub : (fun p : X × ℝ => (p.1, -c * p.2)) '' {p : X × ℝ | -δ < p.2 ∧ p.2 < 0}
      ⊆ {p : X × ℝ | 0 < p.2} := by
    rintro x ⟨p, hp, rfl⟩
    show 0 < -c * p.2
    nlinarith [hcpos, hp.2]
  have hev : ∀ x ∈ (fun p : X × ℝ => (p.1, -c * p.2)) '' {p : X × ℝ | -δ < p.2 ∧ p.2 < 0},
      seeleyV δ g =ᶠ[𝓝 x] g := by
    rintro x ⟨p, hp, rfl⟩
    have hmem : {q : X × ℝ | -(δ / 2) < q.2} ∈ 𝓝 ((p.1, -c * p.2) : X × ℝ) :=
      (isOpen_lt continuous_const continuous_snd).mem_nhds (by
        show -(δ / 2) < -c * p.2
        nlinarith [hδ, hcpos, hp.2])
    filter_upwards [hmem] with q hq
    exact seeleyV_eq δ g (hδ := hδ) (le_of_lt hq)
  refine mul_le_mul' le_rfl ?_
  calc gSN k α (seeleyV δ g)
          ((fun p : X × ℝ => (p.1, -c * p.2)) '' {p : X × ℝ | -δ < p.2 ∧ p.2 < 0})
      = gSN k α g ((fun p : X × ℝ => (p.1, -c * p.2)) '' {p : X × ℝ | -δ < p.2 ∧ p.2 < 0}) :=
        gSN_eq_of_eventuallyEq hev k α
    _ ≤ gSN k α g {p : X × ℝ | 0 < p.2} := gSN_mono hsub k α g

/-! ## Elementary arithmetic helpers -/

/-- `b ^ (j + 1 + α) * b ^ (i - j) = b ^ (i + 1 + α)` for `b > 0` and `j ≤ i`. -/
lemma real_rpow_mul_pow {bb : ℝ} (hb : 0 < bb) {j i : ℕ} (hij : j ≤ i) {α : ℝ} :
    bb ^ ((j : ℝ) + 1 + α) * bb ^ (i - j) = bb ^ ((i : ℝ) + 1 + α) := by
  rw [← Real.rpow_natCast bb (i - j), ← Real.rpow_add hb]
  congr 1
  rw [Nat.cast_sub hij]
  ring

/-- `b ^ j * b ^ ((i - j) + α) = b ^ (i + α)` for `b > 0` and `j ≤ i`. -/
lemma real_pow_mul_rpow {bb : ℝ} (hb : 0 < bb) {j i : ℕ} (hij : j ≤ i) {α : ℝ} :
    bb ^ j * bb ^ ((i - j : ℕ) + α) = bb ^ ((i : ℝ) + α) := by
  rw [← Real.rpow_natCast bb j, ← Real.rpow_add hb]
  congr 1
  rw [Nat.cast_sub hij]
  ring

/-- Reassociation of a product of two `ofReal`s and an arbitrary extended nonnegative real. -/
lemma ofReal_mul_ofReal_mul {p q : ℝ} (hp : 0 ≤ p) (_hq : 0 ≤ q) (Z : ℝ≥0∞) :
    ENNReal.ofReal p * (ENNReal.ofReal q * Z) = ENNReal.ofReal (p * q) * Z := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul hp]

/-- Reassociation of a product of three `ofReal`s and an arbitrary extended nonnegative real. -/
lemma ofReal_three_mul {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (Z : ℝ≥0∞) :
    ENNReal.ofReal p * (ENNReal.ofReal q * (ENNReal.ofReal r * Z))
      = ENNReal.ofReal (p * (q * r)) * Z := by
  rw [ofReal_mul_ofReal_mul hq hr Z, ofReal_mul_ofReal_mul hp (mul_nonneg hq hr) Z]

/-- Reindexing `∑_{j < i+1} f (i - j) = ∑_{j < i+1} f j`. -/
lemma sum_range_sub_eq (f : ℕ → ℝ≥0∞) (i : ℕ) :
    (∑ j ∈ Finset.range (i + 1), f (i - j)) = ∑ j ∈ Finset.range (i + 1), f j := by
  have h := Finset.sum_range_reflect f (i + 1)
  simpa using h

/-! ## The main bound -/

noncomputable def lsmulL : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ

set_option maxHeartbeats 1000000 in
/-- Hölder-seminorm bound for the `m`-th Seeley term over the open lower slab, with a constant
uniform in `m` (the explicit `m`-dependence is `|a m| * (b m)^(i+2)`; the extra two powers absorb
the `α ≤ 1` exponent from the cutoff seminorm bound `gSN_cutoff_le`). -/
theorem seeleyTV_hSN_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {δ : ℝ} (hδ : 0 < δ) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {a b : ℕ → ℝ}
    (hb1 : ∀ m, 1 ≤ b m) {g : X × ℝ → ℂ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) g {p : X × ℝ | -δ < p.2}) (i : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
      Work.CR.Flat.Holder.hSN i α (Work.NN.Final.seeleyTV a b δ g m)
          {p : X × ℝ | -δ < p.2 ∧ p.2 < 0}
        ≤ ENNReal.ofReal (|a m| * (b m) ^ (i + 2) * C) *
            (∑ j ∈ Finset.range (i + 1),
              (Work.CR.Flat.Holder.iDN j g {p : X × ℝ | 0 < p.2}
                + Work.CR.Flat.Holder.hSN j α g {p : X × ℝ | 0 < p.2})) := by
  -- the constant
  set Mc : ℝ := ∑ j ∈ Finset.range (i + 1),
      (i.choose j : ℝ) * (2 * seeleyCutB j + seeleyCutB (j + 1) + seeleyCutB j) with hMc
  set M : ℝ := 1 + Mc with hM
  have hMc_nonneg : 0 ≤ Mc := by
    rw [hMc]
    refine Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) ?_
    have h1 := seeleyCutB_nonneg j
    have h2 := seeleyCutB_nonneg (j + 1)
    linarith
  have hMpos : 0 < M := by rw [hM]; linarith
  refine ⟨‖lsmulL‖ * M + 1, by linarith [mul_nonneg (norm_nonneg lsmulL) hMpos.le], ?_⟩
  intro m
  -- the two open sets
  set Ω : Set (X × ℝ) := {p : X × ℝ | -δ < p.2 ∧ p.2 < 0} with hΩ
  set U : Set (X × ℝ) := {p : X × ℝ | 0 < p.2} with hU
  have hΩopen : IsOpen Ω := by
    rw [hΩ]
    exact (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const)
  have hUopen : IsOpen U := by
    rw [hU]
    exact isOpen_lt continuous_const continuous_snd
  -- replace `hSN` by `gSN`, and `iDN`/`hSN` over the open set `U` by `gDN`/`gSN`
  rw [← gSN_eq_hSN hΩopen i α (seeleyTV a b δ g m)]
  have hS : (∑ j ∈ Finset.range (i + 1),
        (Work.CR.Flat.Holder.iDN j g U + Work.CR.Flat.Holder.hSN j α g U))
      = ∑ j ∈ Finset.range (i + 1), (gDN j g U + gSN j α g U) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← gDN_eq_iDN hUopen j g, ← gSN_eq_hSN hUopen j α g]
  rw [hS]
  -- the product decomposition
  set χ : X × ℝ → ℝ := fun p => seeleyCut (-(b m) * p.2) with hχ
  set Ψ : X × ℝ → ℂ := fun p => seeleyV δ g (p.1, -(b m) * p.2) with hΨ
  have hTV : seeleyTV a b δ g m = fun p : X × ℝ => ((a m) • lsmulL) (χ p) (Ψ p) := by
    funext p
    simp only [hχ, hΨ, seeleyTV, lsmulL, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.lsmul_apply, smul_smul]
  rw [hTV]
  -- smoothness
  have hχsmooth : ContDiff ℝ (i : WithTop ℕ∞) χ := by
    rw [hχ]
    have harg : ContDiff ℝ ∞ (fun p : X × ℝ => -(b m) * p.2) :=
      ContinuousLinearMap.contDiff ((-(b m)) • ContinuousLinearMap.snd ℝ X ℝ)
    exact (seeleyCut_contDiff.comp harg).of_le (by simp)
  have hΨsmooth : ContDiff ℝ (i : WithTop ℕ∞) Ψ := by
    rw [hΨ]
    have hv : ContDiff ℝ ∞ (seeleyV δ g) := seeleyV_contDiff hδ hg
    have hshear : ContDiff ℝ ∞ (fun p : X × ℝ => (p.1, -(b m) * p.2)) :=
      ContinuousLinearMap.contDiff (seeleyLam (X := X) (-(b m)))
    exact (hv.comp hshear).of_le (by simp)
  -- the bilinear Leibniz bound
  have hbil := gSN_bilinear_le ((a m) • lsmulL) i α hχsmooth hΨsmooth (Ω := Ω)
  refine hbil.trans ?_
  -- the four ingredient bounds
  have hχSN : ∀ j, j ≤ i → gSN j α χ Ω ≤
      ENNReal.ofReal ((b m) ^ ((j : ℝ) + 1 + α) * (2 * seeleyCutB j + seeleyCutB (j + 1))) := by
    intro j hj
    have hc : (1 : ℝ) ≤ |(-(b m))| := by
      rw [abs_neg, abs_of_nonneg (by linarith [hb1 m])]
      exact hb1 m
    have h := gSN_cutoff_le (X := X) (c := -(b m)) (i := j) (α := α) (Ω := Ω) hc hα hα1
    rw [hχ]
    refine h.trans (le_of_eq ?_)
    rw [abs_neg, abs_of_nonneg (by linarith [hb1 m])]
  have hχDN : ∀ j, j ≤ i → gDN j χ Ω ≤ ENNReal.ofReal ((b m) ^ j * seeleyCutB j) := by
    intro j hj
    have h := gDN_cutoff_le (X := X) (c := -(b m)) (i := j) (Ω := Ω)
    rw [hχ]
    refine h.trans (le_of_eq ?_)
    rw [abs_neg, abs_of_nonneg (by linarith [hb1 m])]
  have hΨDN : ∀ j, j ≤ i → gDN j Ψ Ω ≤ ENNReal.ofReal ((b m) ^ j) * gDN j g U := by
    intro j hj
    rw [hΨ]
    exact gDN_seeleyV_shear_le hδ hg (hb1 m) j
  have hΨSN : ∀ j, j ≤ i → gSN j α Ψ Ω ≤ ENNReal.ofReal ((b m) ^ ((j : ℝ) + α)) * gSN j α g U := by
    intro j hj
    rw [hΨ]
    exact gSN_seeleyV_shear_le hδ hg (hb1 m) j hα
  -- the coefficient bounds
  have hcoef : ∀ j ∈ Finset.range (i + 1),
      (i.choose j : ℝ) * (2 * seeleyCutB j + seeleyCutB (j + 1)) ≤ M ∧
      (i.choose j : ℝ) * seeleyCutB j ≤ M := by
    intro j hj
    have hle : (i.choose j : ℝ) *
        (2 * seeleyCutB j + seeleyCutB (j + 1) + seeleyCutB j) ≤ Mc := by
      rw [hMc]
      refine Finset.single_le_sum
        (f := fun k => (i.choose k : ℝ) *
          (2 * seeleyCutB k + seeleyCutB (k + 1) + seeleyCutB k)) ?_ hj
      intro k _
      refine mul_nonneg (by positivity) ?_
      have h1 := seeleyCutB_nonneg k
      have h2 := seeleyCutB_nonneg (k + 1)
      linarith
    have hsb := seeleyCutB_nonneg j
    have hsb' := seeleyCutB_nonneg (j + 1)
    have hcj : (0 : ℝ) ≤ (i.choose j : ℝ) := Nat.cast_nonneg _
    constructor
    · have h' : (i.choose j : ℝ) * (2 * seeleyCutB j + seeleyCutB (j + 1)) ≤
          (i.choose j : ℝ) * (2 * seeleyCutB j + seeleyCutB (j + 1) + seeleyCutB j) := by
        nlinarith [hcj, hsb]
      rw [hM]; linarith
    · have h' : (i.choose j : ℝ) * seeleyCutB j ≤
          (i.choose j : ℝ) * (2 * seeleyCutB j + seeleyCutB (j + 1) + seeleyCutB j) := by
        nlinarith [hcj, hsb, hsb']
      rw [hM]; linarith
  -- the term-by-term bound
  have hterm : ∀ j ∈ Finset.range (i + 1),
      (i.choose j : ENNReal) * (gSN j α χ Ω * gDN (i - j) Ψ Ω + gDN j χ Ω * gSN (i - j) α Ψ Ω)
      ≤ ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) *
          (gDN (i - j) g U + gSN (i - j) α g U) := by
    intro j hj
    have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hij : i - j ≤ i := Nat.sub_le i j
    obtain ⟨hcoefA, hcoefB⟩ := hcoef j hj
    have hb0 : (0 : ℝ) < b m := by linarith [hb1 m]
    have hbge : (1 : ℝ) ≤ b m := hb1 m
    have hbbE : 0 ≤ (b m) ^ ((i : ℝ) + 2) := Real.rpow_nonneg hb0.le _
    have hKnn : 0 ≤ 2 * seeleyCutB j + seeleyCutB (j + 1) := by
      have h1 := seeleyCutB_nonneg j
      have h2 := seeleyCutB_nonneg (j + 1)
      linarith
    have hA := hχSN j hji
    have hB := hΨDN (i - j) hij
    have hC := hχDN j hji
    have hD := hΨSN (i - j) hij
    have htermA : (i.choose j : ENNReal) * (gSN j α χ Ω * gDN (i - j) Ψ Ω)
        ≤ ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) * gDN (i - j) g U := by
      have hmain : (i.choose j : ENNReal) * (gSN j α χ Ω * gDN (i - j) Ψ Ω)
          ≤ ENNReal.ofReal ((i.choose j : ℝ) * ((b m) ^ ((j : ℝ) + 1 + α) *
                (2 * seeleyCutB j + seeleyCutB (j + 1)) * (b m) ^ (i - j)))
              * gDN (i - j) g U := by
        calc (i.choose j : ENNReal) * (gSN j α χ Ω * gDN (i - j) Ψ Ω)
            ≤ (i.choose j : ENNReal) *
                (ENNReal.ofReal ((b m) ^ ((j : ℝ) + 1 + α) *
                    (2 * seeleyCutB j + seeleyCutB (j + 1))) *
                  (ENNReal.ofReal ((b m) ^ (i - j)) * gDN (i - j) g U)) :=
              mul_le_mul' le_rfl (mul_le_mul' hA hB)
          _ = ENNReal.ofReal ((i.choose j : ℝ) * ((b m) ^ ((j : ℝ) + 1 + α) *
                    (2 * seeleyCutB j + seeleyCutB (j + 1)) * (b m) ^ (i - j)))
                * gDN (i - j) g U := by
              rw [← ENNReal.ofReal_natCast (i.choose j),
                ofReal_three_mul (Nat.cast_nonneg _) (mul_nonneg
                  (Real.rpow_nonneg hb0.le _) hKnn) (pow_nonneg hb0.le _) _]
      refine hmain.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
      have hpow : (b m) ^ ((j : ℝ) + 1 + α) * (b m) ^ (i - j) ≤ (b m) ^ ((i : ℝ) + 2) := by
        rw [real_rpow_mul_pow hb0 hji]
        refine Real.rpow_le_rpow_of_exponent_le hbge ?_
        have hji' : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast hji
        linarith
      calc (i.choose j : ℝ) * ((b m) ^ ((j : ℝ) + 1 + α) *
              (2 * seeleyCutB j + seeleyCutB (j + 1)) * (b m) ^ (i - j))
          = ((b m) ^ ((j : ℝ) + 1 + α) * (b m) ^ (i - j)) *
              ((i.choose j : ℝ) * (2 * seeleyCutB j + seeleyCutB (j + 1))) := by ring
        _ ≤ (b m) ^ ((i : ℝ) + 2) * M :=
            mul_le_mul hpow hcoefA (mul_nonneg (by positivity) hKnn) hbbE
    have htermB : (i.choose j : ENNReal) * (gDN j χ Ω * gSN (i - j) α Ψ Ω)
        ≤ ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) * gSN (i - j) α g U := by
      have hmain : (i.choose j : ENNReal) * (gDN j χ Ω * gSN (i - j) α Ψ Ω)
          ≤ ENNReal.ofReal ((i.choose j : ℝ) * ((b m) ^ j * seeleyCutB j *
                (b m) ^ (((i - j : ℕ) : ℝ) + α))) * gSN (i - j) α g U := by
        calc (i.choose j : ENNReal) * (gDN j χ Ω * gSN (i - j) α Ψ Ω)
            ≤ (i.choose j : ENNReal) *
                (ENNReal.ofReal ((b m) ^ j * seeleyCutB j) *
                  (ENNReal.ofReal ((b m) ^ (((i - j : ℕ) : ℝ) + α)) *
                    gSN (i - j) α g U)) :=
              mul_le_mul' le_rfl (mul_le_mul' hC hD)
          _ = ENNReal.ofReal ((i.choose j : ℝ) * ((b m) ^ j * seeleyCutB j *
                    (b m) ^ (((i - j : ℕ) : ℝ) + α))) * gSN (i - j) α g U := by
              rw [← ENNReal.ofReal_natCast (i.choose j),
                ofReal_three_mul (Nat.cast_nonneg _)
                  (mul_nonneg (pow_nonneg hb0.le _) (seeleyCutB_nonneg j))
                  (Real.rpow_nonneg hb0.le _) _]
      refine hmain.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
      have hpow : (b m) ^ j * (b m) ^ (((i - j : ℕ) : ℝ) + α) ≤ (b m) ^ ((i : ℝ) + 2) := by
        rw [real_pow_mul_rpow hb0 hji]
        refine Real.rpow_le_rpow_of_exponent_le hbge ?_
        linarith
      calc (i.choose j : ℝ) * ((b m) ^ j * seeleyCutB j * (b m) ^ (((i - j : ℕ) : ℝ) + α))
          = ((b m) ^ j * (b m) ^ (((i - j : ℕ) : ℝ) + α)) * ((i.choose j : ℝ) * seeleyCutB j) := by
            ring
        _ ≤ (b m) ^ ((i : ℝ) + 2) * M :=
            mul_le_mul hpow hcoefB (mul_nonneg (by positivity) (seeleyCutB_nonneg j)) hbbE
    calc (i.choose j : ENNReal) *
            (gSN j α χ Ω * gDN (i - j) Ψ Ω + gDN j χ Ω * gSN (i - j) α Ψ Ω)
        = (i.choose j : ENNReal) * (gSN j α χ Ω * gDN (i - j) Ψ Ω) +
            (i.choose j : ENNReal) * (gDN j χ Ω * gSN (i - j) α Ψ Ω) := by rw [mul_add]
      _ ≤ ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) * gDN (i - j) g U +
            ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) * gSN (i - j) α g U :=
          add_le_add htermA htermB
      _ = ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) *
            (gDN (i - j) g U + gSN (i - j) α g U) := by rw [← mul_add]
  -- the sum bound
  have hP : (∑ j ∈ Finset.range (i + 1), (i.choose j : ENNReal) *
        (gSN j α χ Ω * gDN (i - j) Ψ Ω + gDN j χ Ω * gSN (i - j) α Ψ Ω))
      ≤ ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) *
          (∑ j ∈ Finset.range (i + 1), (gDN j g U + gSN j α g U)) := by
    rw [← sum_range_sub_eq (fun k => gDN k g U + gSN k α g U) i]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hBmnorm : ‖(a m) • lsmulL‖ ≤ |a m| * ‖lsmulL‖ := by
    simpa only [Real.norm_eq_abs] using ContinuousLinearMap.opNorm_smul_le (a m) lsmulL
  have hbbE : 0 ≤ (b m) ^ ((i : ℝ) + 2) := Real.rpow_nonneg (by linarith [hb1 m]) _
  have hreal : (|a m| * ‖lsmulL‖) * ((b m) ^ ((i : ℝ) + 2) * M)
      ≤ |a m| * (b m) ^ (i + 2) * (‖lsmulL‖ * M + 1) := by
    rw [show (b m) ^ (i + 2) = (b m) ^ ((i : ℝ) + 2) from by
      rw [← Real.rpow_natCast (b m) (i + 2),
        show ((i + 2 : ℕ) : ℝ) = (i : ℝ) + 2 by push_cast; ring]]
    have hkey : (|a m| * ‖lsmulL‖) * ((b m) ^ ((i : ℝ) + 2) * M)
        = |a m| * (b m) ^ ((i : ℝ) + 2) * (‖lsmulL‖ * M) := by ring
    rw [hkey]
    exact mul_le_mul_of_nonneg_left (by linarith)
      (mul_nonneg (abs_nonneg _) hbbE)
  calc ENNReal.ofReal ‖(a m) • lsmulL‖ *
        (∑ j ∈ Finset.range (i + 1), (i.choose j : ENNReal) *
          (gSN j α χ Ω * gDN (i - j) Ψ Ω + gDN j χ Ω * gSN (i - j) α Ψ Ω))
      ≤ ENNReal.ofReal ‖(a m) • lsmulL‖ *
          (ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) *
            (∑ j ∈ Finset.range (i + 1), (gDN j g U + gSN j α g U))) :=
        mul_le_mul' le_rfl hP
    _ ≤ ENNReal.ofReal (|a m| * ‖lsmulL‖) *
          (ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) *
            (∑ j ∈ Finset.range (i + 1), (gDN j g U + gSN j α g U))) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hBmnorm) le_rfl
    _ = ENNReal.ofReal ((|a m| * ‖lsmulL‖) * ((b m) ^ ((i : ℝ) + 2) * M)) *
          (∑ j ∈ Finset.range (i + 1), (gDN j g U + gSN j α g U)) :=
        ofReal_mul_ofReal_mul (mul_nonneg (abs_nonneg (a m)) (norm_nonneg lsmulL))
          (mul_nonneg hbbE hMpos.le) _
    _ ≤ ENNReal.ofReal (|a m| * (b m) ^ (i + 2) * (‖lsmulL‖ * M + 1)) *
          (∑ j ∈ Finset.range (i + 1), (gDN j g U + gSN j α g U)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl

end Work.NN.Seeley
