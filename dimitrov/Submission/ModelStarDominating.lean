import Mathlib
import Submission.ModelStarN1
import Submission.ModelStarChebyshev
import Submission.Step3Bridge
import Submission.DubininMap

/-!
# ModelStarDominating -- the "dominating model star" bound for hedgehog capacity

STATUS: research isolate (NOT imported by `Submission.lean`); 0 sorries;
every declaration axiom-clean `[propext, Classical.choice, Quot.sound]`.

## The idea

The gate `Submission.Step3.sym_maximality` (Dubinin's hedgehog inequality)

    limsup_n (feketeNumber (dirStar u L) (n+1))^(2/((n+1)n))  ≤  L · 4^(-1/s),  s = |u|,

is, by `Step3Bridge.sym_maximality_of_unit`, equivalent to its unit-length
instance.  The present module proves a NEW reduction of that instance to a
statement about the *explicit* model map

    F = modelF z₀ r,      M := modelStarImage z₀ r = F '' unitCircle,

namely:

    if `dirStar u θ ⊆ M`   then   limsup_n rootSeq u 1 n  ≤  1/θ .        (DOM)

Here `dirStar u θ = ⋃_{w ∈ u} [0, θ·w]` is the hedgehog with `s = |u|` spikes of
common length `θ` in the directions `u`, and `rootSeq u 1` is the Step3 root
sequence.  In other words: **if a normalised model star contains the hedgehog
with spike length `θ`, then the unit hedgehog has transfinite diameter at most
`1/θ`.**

The proof is three lines of bookkeeping on the already-proved structure of the
model star:
  * `Submission.ModelStarN1.fekete_rootLimsup_modelStar_le_one` -- the model
    star has transfinite diameter ≤ 1 (Fekete's hard half for model stars);
  * `Submission.ModelStarChebyshev.one_le_feketeNumber_modelStar` (the easy
    half) -- together: `transfinite diameter of M = 1`
    (`modelStar_feketeRootLimsup_eq_one` below);
  * `Submission.Step3Scaling.feketeRoot_scaling` -- Fekete-numbers/roots scale
    by the homothety factor;
  * `Submission.DubininMap.feketeNumber_mono` -- monotonicity in the set.

## Why this is the right shape for the remaining gap

The remaining input of the Eremenko/ModelStar programme has always been
"the hedgehog is, up to scale, a model star of its own junction data"
(E1/E3, the conformal boundary correspondence).  (DOM) shows that only the
following *much weaker, purely model-theoretic* existence statement is needed:

    for every finite set `u` of `s ≥ 1` distinct unit directions there are
    standard model data `(z₀, r, φ)` with `s` junctions and a length
    `θ ≥ 4^(1/s)` such that `dirStar u θ ⊆ modelStarImage z₀ r`.        (EX)

Indeed (EX) + (DOM) give `limsup rootSeq u 1 ≤ 1/θ ≤ 4^(-1/s)`, which is
exactly the unit case of `Step3.sym_maximality`.  Statement (EX) involves only
the explicit map `F(z) = z·∏_k (1 - z₀ k/z)^(2 r k)`, its arc structure
(`ModelStarImageSeg.ArcGood`: each arc of the circle maps onto a segment
`[0,m]·u`) and elementary trigonometry -- no Carathéodory theory, no conformal
map of a general domain.

Equality in (EX) holds for the equiangular configuration with the symmetric
data (`z₀ k = eAngle (2πk/s)`, `r k = 1/s`), whose model star has all `s` tips
exactly `4^(1/s)`; `ModelStarTipBound.max_tip_ge_four_rpow_inv` (the
Konyagin-Lev circle inequality) is the statement that `max` of the tips is
always `≥ 4^(1/s)`, i.e. the `max` version of (EX).  (EX) is the `min` version.
See `Submission/Work/STATUS_dimitrov.md` section 126 for the numerical evidence
(random configurations satisfy (EX) with a comfortable margin, whereas the
"bisector" canonical choice satisfies it only up to ~2%).

## Contents

* `modelStar_feketeRootLimsup_eq_one` -- the model star has transfinite
  diameter exactly `1`.
* `rootSeq_one_le_inv_theta` -- (DOM) for an arbitrary dominating set `K` of
  transfinite diameter ≤ 1 (not just a model star).
* `rootSeq_one_le_inv_theta_of_modelStar` -- (DOM) for model stars.
* `sym_maximality_of_dominating` -- (EX) implies the `L = 1` case of
  `Step3.sym_maximality` (the full statement follows by
  `Step3Bridge.sym_maximality_of_unit`).
-/

noncomputable section

open scoped Real Topology BigOperators
open Filter Set

namespace Submission.ModelStarDominating

open Submission.FeketeLim
open Submission.Step3
open Submission.Step3Scaling
open Submission.Step3Bridge

variable {s : ℕ} {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ}

/-! ## Homothety bookkeeping -/

/-- Homotheties compose. -/
lemma homot_homot (a b : ℂ) (S : Set ℂ) :
    homot a (homot b S) = homot (a * b) S := by
  unfold homot
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by ring⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨b * z, ⟨z, hz, rfl⟩, by ring⟩

/-- Composition of homotheties, image form (matching `Step3Scaling.homot`'s
definition). -/
lemma homot_homot_image (a b : ℂ) (S : Set ℂ) :
    homot a ((fun z : ℂ => b * z) '' S) = homot (a * b) S := by
  unfold homot
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by ring⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨b * z, ⟨z, hz, rfl⟩, by ring⟩

/-- The identity homothety is the identity. -/
lemma homot_one (S : Set ℂ) : homot (1 : ℂ) S = S := by
  unfold homot
  ext x
  constructor
  · rintro ⟨y, hy, hfl⟩
    rw [← hfl]
    simpa using hy
  · intro hx
    exact ⟨x, hx, one_mul x⟩

/-! ## The transfinite diameter of the model star is `1` -/

/-- The root sequence of the model star (same exponent convention as
`Step3Bridge.rootSeq`, indexed by `N`). -/
def starRoot (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (N : ℕ) : ℝ :=
  (feketeNumber (Submission.ModelStarExterior.modelStarImage z₀ r) N) ^
    (2 / ((N : ℝ) * ((N : ℝ) - 1)))

/-- Every point of the model star `M = modelF z₀ r '' unitCircle` has modulus at
most `4`. -/
lemma modelStar_norm_le_four {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ}
    (hz₀e : ∀ k : Fin s, z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hsum : (∑ k : Fin s, r k) = 1) (hr : ∀ k : Fin s, 0 < r k) :
    ∀ w ∈ Submission.ModelStarExterior.modelStarImage z₀ r, ‖w‖ ≤ 4 := by
  rintro w ⟨v, hv, rfl⟩
  obtain ⟨t, _, _, rfl⟩ := Submission.ModelStarImageSeg.exists_eAngle_eq_of_mem_circle hv
  rw [← Submission.ModelStarBoundary3.rho_eq_norm_boundary z₀ φ r hz₀e]
  exact Submission.ModelStarImageSeg.rho_le_four (φ := φ) (r := r) hsum
    (fun k => le_of_lt (hr k)) t

/-- **The model star has transfinite diameter exactly one.**  (Upper bound:
`ModelStarN1`; lower bound: `ModelStarChebyshev`.) -/
theorem modelStar_feketeRootLimsup_eq_one (hs : 0 < s)
    (hz₀e : ∀ k : Fin s, z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k : Fin s, ‖z₀ k‖ = 1) (hr : ∀ k : Fin s, 0 < r k)
    (hsum : (∑ k : Fin s, r k) = 1) (hmono : Monotone φ)
    (hφinj : Function.Injective φ) (hφlo : ∀ k : Fin s, 0 ≤ φ k)
    (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi) :
    Filter.limsup (starRoot z₀ r) Filter.atTop = 1 := by
  have hle := Submission.ModelStarN1.fekete_rootLimsup_modelStar_le_one hs hz₀e hunit hr
    hsum hmono hφinj hφlo hφhi
  refine le_antisymm hle ?_
  -- lower bound: each term with N ≥ 2 is at least 1
  have hge : ∀ᶠ N : ℕ in Filter.atTop, (1 : ℝ) ≤ starRoot z₀ r N := by
    filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    have hN1 : 1 ≤ N := le_trans (by norm_num) hN
    have hm : 1 ≤ feketeNumber (Submission.ModelStarExterior.modelStarImage z₀ r) N :=
      Submission.ModelStarChebyshev.one_le_feketeNumber_modelStar hunit hr hs N hN1
    have hexp : 0 ≤ 2 / ((N : ℝ) * ((N : ℝ) - 1)) := by
      apply div_nonneg (by norm_num)
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
      have h2 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      positivity
    calc (1 : ℝ) = (1 : ℝ) ^ (2 / ((N : ℝ) * ((N : ℝ) - 1))) := (Real.one_rpow _).symm
      _ ≤ _ := Real.rpow_le_rpow zero_le_one hm hexp
  refine Filter.le_limsup_of_frequently_le hge.frequently ?_
  -- boundedness above of the sequence (crude: the model star lies in the ball of radius 4)
  have hMnorm : ∀ w ∈ Submission.ModelStarExterior.modelStarImage z₀ r, ‖w‖ ≤ 4 :=
    modelStar_norm_le_four hz₀e hsum hr
  have hne : (Submission.ModelStarExterior.modelStarImage z₀ r).Nonempty :=
    ⟨0, ⟨z₀ ⟨0, hs⟩, Submission.ModelStarExterior.mem_circle.mpr (hunit _),
      Submission.ModelStarExterior.modelF_junction_eq_zero z₀ r hunit hr ⟨0, hs⟩⟩⟩
  have hKb : Bornology.IsBounded (Submission.ModelStarExterior.modelStarImage z₀ r) :=
    (Submission.ModelStarExterior.isCompact_modelStarImage z₀ r hunit hr).isBounded
  have hbdd : ∀ N : ℕ, starRoot z₀ r N ≤ (max 1 8 : ℝ) ^ 4 := by
    intro N
    rcases N with _ | n
    · show (feketeNumber (Submission.ModelStarExterior.modelStarImage z₀ r) 0) ^
          (2 / (((0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) - 1))) ≤ (max 1 8 : ℝ) ^ 4
      rw [show (2 : ℝ) / (((0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) - 1)) = 0 from by norm_num,
        Real.rpow_zero]
      exact one_le_pow₀ (le_max_left 1 8)
    · have hkey := feketeRoot_bounded (K := Submission.ModelStarExterior.modelStarImage z₀ r)
        hne hKb (R := 4) (by norm_num) hMnorm n
      have hbase : (max 1 (2 * 4) : ℝ) = max 1 8 := by norm_num
      rw [hbase] at hkey
      show (feketeNumber (Submission.ModelStarExterior.modelStarImage z₀ r) (n + 1)) ^
          (2 / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1))) ≤ (max 1 8 : ℝ) ^ 4
      have hexp : 2 / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1))
          = 2 / (((n : ℝ) + 1) * (n : ℝ)) := by
        push_cast
        ring_nf
      rw [hexp]
      exact hkey
  exact Filter.isBoundedUnder_of (f := Filter.atTop) ⟨(max 1 8 : ℝ) ^ 4, fun n => hbdd n⟩


/-! ## The main reduction -/

/-- Uniform bound for the `N`-indexed Fekete-root sequence of a set contained in
the closed ball of radius `R`. -/
lemma root_le_of_norm_le {K : Set ℂ} {R : ℝ} (hKne : K.Nonempty)
    (hKb : Bornology.IsBounded K) (hR0 : 0 ≤ R) (hRK : ∀ z ∈ K, ‖z‖ ≤ R) (N : ℕ) :
    (feketeNumber K N) ^ (2 / ((N : ℝ) * ((N : ℝ) - 1))) ≤ (max 1 (2 * R)) ^ 4 := by
  rcases N with _ | n
  · show (feketeNumber K 0) ^ (2 / (((0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) - 1)))
      ≤ (max 1 (2 * R)) ^ 4
    rw [show (2 : ℝ) / ((((0 : ℕ)) : ℝ) * ((((0 : ℕ)) : ℝ) - 1)) = 0 from by norm_num,
      Real.rpow_zero]
    exact one_le_pow₀ (le_max_left 1 (2 * R))
  · have h := feketeRoot_bounded (K := K) hKne hKb hR0 hRK n
    convert h using 2
    push_cast
    ring_nf

/-- **(DOM), the "dominating model star" bound.**  Let `u` be a finite set of
unit directions with `s = |u| ≥ 1`, let `θ > 0`, and let `K` be a set containing
the hedgehog `dirStar u θ` (the union of the `s` segments `[0, θ·w]`, `w ∈ u`).
If the transfinite diameter of `K` (Fekete-root limsup) is at most `1`, then the
transfinite diameter of the unit hedgehog `dirStar u 1` is at most `1/θ`. -/
theorem rootSeq_one_le_inv_theta {u : Finset ℂ} (hu : ∀ w ∈ u, ‖w‖ = 1)
    (hs : 1 ≤ u.card) {θ : ℝ} (hθ : 0 < θ) {K : Set ℂ} {R : ℝ} (hR0 : 0 ≤ R)
    (hRK : ∀ z ∈ K, ‖z‖ ≤ R) (hKne : K.Nonempty) (hKb : Bornology.IsBounded K)
    (hsub : dirStar u θ ⊆ K)
    (hcap : Filter.limsup (fun N : ℕ =>
      (feketeNumber K N) ^ (2 / ((N : ℝ) * ((N : ℝ) - 1)))) Filter.atTop ≤ 1) :
    Filter.limsup (rootSeq u 1) Filter.atTop ≤ 1 / θ := by
  have huN : u.Nonempty := Finset.card_pos.mp hs
  have hKneθ : (dirStar u θ).Nonempty := dirStar_nonempty huN θ
  have hKbθ : Bornology.IsBounded (dirStar u θ) := dirStar_isBounded u hu θ (le_of_lt hθ)
  -- the homothety identity `dirStar u 1 = (1/θ) · (dirStar u θ)`
  have hset : dirStar u 1 = homot (((1 / θ : ℝ) : ℂ)) (dirStar u θ) := by
    rw [dirStar_eq_homot u θ, homot_homot_image]
    have hmul : (((1 / θ : ℝ) : ℂ)) * ((θ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, one_div, inv_mul_cancel₀ (ne_of_gt hθ), Complex.ofReal_one]
    rw [hmul, homot_one]
  -- pointwise bound for `n ≥ 1`
  have key : ∀ n : ℕ, 1 ≤ n → rootSeq u 1 n ≤ (1 / θ) *
      (feketeNumber K (n + 1)) ^ (2 / ((n + 1 : ℝ) * (n : ℝ))) := by
    intro n hn
    have hsc := feketeRoot_scaling (K := dirStar u θ) hKneθ hKbθ (((1 / θ : ℝ) : ℂ)) hn
    have hnorm : ‖(((1 / θ : ℝ) : ℂ))‖ = 1 / θ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hstep : rootSeq u 1 n =
        (feketeNumber (homot (((1 / θ : ℝ) : ℂ)) (dirStar u θ)) (n + 1)) ^
          (2 / ((n + 1 : ℝ) * (n : ℝ))) := by
      unfold rootSeq
      rw [hset]
    rw [hstep, hsc, hnorm]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hmono := Submission.DubininMap.feketeNumber_mono (K := dirStar u θ) (K' := K) hsub
      (n + 1) (Submission.DubininMap.feketeSet_nonempty_of_nonempty hKneθ (n + 1))
      (feketeSet_bddAbove_of_bounded hKb (n + 1))
    have h0 : 0 ≤ feketeNumber (dirStar u θ) (n + 1) := feketeNumber_nonneg hKneθ hKbθ (n + 1)
    have hp : 0 ≤ 2 / ((n + 1 : ℝ) * (n : ℝ)) := by
      apply div_nonneg (by norm_num)
      positivity
    exact Real.rpow_le_rpow h0 hmono hp
  -- bounds for the `K` root sequence (for the limsup API)
  have hKbd : ∀ N : ℕ, (feketeNumber K N) ^ (2 / ((N : ℝ) * ((N : ℝ) - 1)))
      ≤ (max 1 (2 * R)) ^ 4 := root_le_of_norm_le hKne hKb hR0 hRK
  have hcobK : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
      (fun N : ℕ => (feketeNumber K N) ^ (2 / ((N : ℝ) * ((N : ℝ) - 1)))) :=
    Filter.isCoboundedUnder_le_of_le Filter.atTop (x := 0) (fun N =>
      Real.rpow_nonneg (feketeNumber_nonneg hKne hKb N) _)
  have hbddK : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun N : ℕ => (feketeNumber K N) ^ (2 / ((N : ℝ) * ((N : ℝ) - 1)))) :=
    Filter.isBoundedUnder_of (f := Filter.atTop) ⟨(max 1 (2 * R)) ^ 4, fun N => hKbd N⟩
  -- conclude: limsup ≤ 1/θ + ε for every ε > 0
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have hεθ : 0 < ε * θ := mul_pos hε hθ
  have hev : ∀ᶠ n : ℕ in Filter.atTop, rootSeq u 1 n ≤ 1 / θ + ε := by
    have hlt := (Filter.limsup_le_iff hcobK hbddK).mp hcap (1 + ε * θ) (by linarith)
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hlt
    filter_upwards [Filter.eventually_ge_atTop (max 1 N₀)] with n hn
    have hn1 : 1 ≤ n := le_trans (le_max_left 1 N₀) hn
    have hnN : N₀ ≤ n := le_trans (le_max_right 1 N₀) hn
    have hb := hN₀ (n + 1) (by omega)
    have hexp : 2 / ((((n + 1 : ℕ)) : ℝ) * ((((n + 1 : ℕ)) : ℝ) - 1))
        = 2 / ((n + 1 : ℝ) * (n : ℝ)) := by
      push_cast
      ring_nf
    rw [hexp] at hb
    have hkey := key n hn1
    calc rootSeq u 1 n ≤ (1 / θ) * (feketeNumber K (n + 1)) ^ (2 / ((n + 1 : ℝ) * (n : ℝ))) := hkey
      _ ≤ (1 / θ) * (1 + ε * θ) := by
            refine mul_le_mul_of_nonneg_left (le_of_lt hb) (by positivity)
      _ = 1 / θ + ε := by
            field_simp
  exact Filter.limsup_le_of_le
    (Filter.isCoboundedUnder_le_of_le Filter.atTop (x := 0) (fun n => rootSeq_nonneg u 1 n)) hev


/-- `dirStar` is monotone in the spike length. -/
lemma dirStar_subset_of_le {u : Finset ℂ} {L L' : ℝ} (hL : 0 ≤ L) (h : L ≤ L') :
    dirStar u L ⊆ dirStar u L' := by
  rintro z ⟨v, hv, hseg⟩
  refine ⟨v, hv, ?_⟩
  obtain ⟨t, ht, rfl⟩ := (Submission.XTransfer.mem_segment_zero_iff ((L : ℂ) * v) z).1 hseg
  rcases eq_or_lt_of_le hL with h0 | hpos
  · subst h0
    convert (Submission.XTransfer.mem_segment_zero_iff ((L' : ℂ) * v) (0 : ℂ)).2
      ⟨0, ⟨le_refl 0, zero_le_one⟩, by simp⟩ using 1
    simp
  · have hL'pos : 0 < L' := lt_of_lt_of_le hpos h
    refine (Submission.XTransfer.mem_segment_zero_iff ((L' : ℂ) * v)
      (t • ((L : ℂ) * v))).2 ⟨t * L / L',
        ⟨div_nonneg (mul_nonneg ht.1 hpos.le) hL'pos.le, ?_⟩, ?_⟩
    · rw [div_le_one hL'pos]
      nlinarith [ht.2, hpos.le, h]
    · show ((t : ℂ) * ((L : ℂ) * v)) = (((t * L / L' : ℝ)) : ℂ) * ((L' : ℂ) * v)
      rw [← mul_assoc, ← Complex.ofReal_mul, ← mul_assoc, ← Complex.ofReal_mul]
      congr 1
      field_simp

/-- **(DOM) for model stars.**  If the hedgehog `dirStar u θ` with unit directions
`u` and spike length `θ > 0` is contained in the (normalised) model star of the
standard data `(z₀, r, φ)`, then the unit hedgehog has transfinite diameter at
most `1/θ`. -/
theorem rootSeq_one_le_inv_theta_of_modelStar {u : Finset ℂ} (hu : ∀ w ∈ u, ‖w‖ = 1)
    (hs : 1 ≤ u.card) {θ : ℝ} (hθ : 0 < θ) {s' : ℕ} {z₀ : Fin s' → ℂ} {r φ : Fin s' → ℝ}
    (hs' : 0 < s') (hz₀e : ∀ k : Fin s', z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k : Fin s', ‖z₀ k‖ = 1) (hr : ∀ k : Fin s', 0 < r k)
    (hsum : (∑ k : Fin s', r k) = 1) (hmono : Monotone φ)
    (hφinj : Function.Injective φ) (hφlo : ∀ k : Fin s', 0 ≤ φ k)
    (hφhi : ∀ k : Fin s', φ k < 2 * Real.pi)
    (hsub : dirStar u θ ⊆ Submission.ModelStarExterior.modelStarImage z₀ r) :
    Filter.limsup (rootSeq u 1) Filter.atTop ≤ 1 / θ := by
  have hne : (Submission.ModelStarExterior.modelStarImage z₀ r).Nonempty :=
    ⟨0, ⟨z₀ ⟨0, hs'⟩, Submission.ModelStarExterior.mem_circle.mpr (hunit _),
      Submission.ModelStarExterior.modelF_junction_eq_zero z₀ r hunit hr ⟨0, hs'⟩⟩⟩
  have hKb : Bornology.IsBounded (Submission.ModelStarExterior.modelStarImage z₀ r) :=
    (Submission.ModelStarExterior.isCompact_modelStarImage z₀ r hunit hr).isBounded
  have hcap : Filter.limsup (starRoot z₀ r) Filter.atTop ≤ 1 :=
    le_of_eq (modelStar_feketeRootLimsup_eq_one hs' hz₀e hunit hr hsum hmono hφinj hφlo hφhi)
  exact rootSeq_one_le_inv_theta hu hs hθ (R := 4) (by norm_num)
    (modelStar_norm_le_four hz₀e hsum hr) hne hKb hsub hcap

/-- **(DOM) in the sharp shape needed for the gate.**  If some normalised model
star contains the hedgehog with `s` spikes of length `4^(1/s)`, then the unit
hedgehog has transfinite diameter at most `4^(-1/s)`. -/
theorem rootSeq_one_le_four_rpow_inv_of_modelStar {u : Finset ℂ}
    (hu : ∀ w ∈ u, ‖w‖ = 1) (hs : 1 ≤ u.card) {s' : ℕ} {z₀ : Fin s' → ℂ} {r φ : Fin s' → ℝ}
    (hs' : 0 < s') (hz₀e : ∀ k : Fin s', z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k : Fin s', ‖z₀ k‖ = 1) (hr : ∀ k : Fin s', 0 < r k)
    (hsum : (∑ k : Fin s', r k) = 1) (hmono : Monotone φ)
    (hφinj : Function.Injective φ) (hφlo : ∀ k : Fin s', 0 ≤ φ k)
    (hφhi : ∀ k : Fin s', φ k < 2 * Real.pi)
    (hsub : dirStar u ((4 : ℝ) ^ (1 / (u.card : ℝ))) ⊆
      Submission.ModelStarExterior.modelStarImage z₀ r) :
    Filter.limsup (rootSeq u 1) Filter.atTop ≤ (4 : ℝ) ^ (-1 / (u.card : ℝ)) := by
  have hcard : (0 : ℝ) < (u.card : ℝ) := by exact_mod_cast hs
  have hθ : (0 : ℝ) < (4 : ℝ) ^ (1 / (u.card : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have h := rootSeq_one_le_inv_theta_of_modelStar hu hs hθ hs' hz₀e hunit hr hsum hmono
    hφinj hφlo hφhi hsub
  have hinv : 1 / (4 : ℝ) ^ (1 / (u.card : ℝ)) = (4 : ℝ) ^ (-1 / (u.card : ℝ)) := by
    rw [one_div, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4)]
    ring_nf
  rwa [hinv] at h

/-- **(EX), the single remaining input, in the sharp shape.**  `dirStar u μ` is
the hedgehog with `|u|` spikes of common length `μ` in the unit directions `u`.
If for every configuration `u` there is a normalised model star (standard data,
any number `s' ≥ 1` of junctions) containing `dirStar u μ` for some `μ ≥ 4^(1/|u|)`,
then the `L = 1` case of `Step3.sym_maximality` holds:

    limsup_n rootSeq u 1 n  ≤  4^(-1/|u|) .

(Together with `Step3Bridge.sym_maximality_of_unit` this gives the full
`Step3.sym_maximality`, i.e. the gate.) -/
theorem unit_case_of_dominating_modelStar
    (hex : ∀ (u : Finset ℂ), (∀ w ∈ u, ‖w‖ = 1) → 1 ≤ u.card →
      ∃ (s' : ℕ) (z₀ : Fin s' → ℂ) (r φ : Fin s' → ℝ) (μ : ℝ),
        0 < s' ∧
        (∀ k : Fin s', z₀ k = Submission.ModelStarBoundary2.eAngle (φ k)) ∧
        (∀ k : Fin s', ‖z₀ k‖ = 1) ∧ (∀ k : Fin s', 0 < r k) ∧
        (∑ k : Fin s', r k) = 1 ∧ Monotone φ ∧ Function.Injective φ ∧
        (∀ k : Fin s', 0 ≤ φ k) ∧ (∀ k : Fin s', φ k < 2 * Real.pi) ∧
        (4 : ℝ) ^ (1 / (u.card : ℝ)) ≤ μ ∧
        dirStar u μ ⊆ Submission.ModelStarExterior.modelStarImage z₀ r) :
    ∀ (u : Finset ℂ) (hu : ∀ w ∈ u, ‖w‖ = 1) (hs : 1 ≤ u.card),
      Filter.limsup (rootSeq u 1) Filter.atTop ≤ (4 : ℝ) ^ (-1 / (u.card : ℝ)) := by
  intro u hu hs
  obtain ⟨s', z₀, r, φ, μ, hs', hz₀e, hunit, hr, hsum, hmono, hφinj, hφlo, hφhi, hμ, hsub⟩ :=
    hex u hu hs
  have hθ : 0 < (4 : ℝ) ^ (1 / (u.card : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hsub' : dirStar u ((4 : ℝ) ^ (1 / (u.card : ℝ))) ⊆
      Submission.ModelStarExterior.modelStarImage z₀ r :=
    Subset.trans (dirStar_subset_of_le (Real.rpow_nonneg (by norm_num) _) hμ) hsub
  exact rootSeq_one_le_four_rpow_inv_of_modelStar hu hs hs' hz₀e hunit hr hsum hmono hφinj
    hφlo hφhi hsub'

end Submission.ModelStarDominating