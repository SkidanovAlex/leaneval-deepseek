import Mathlib
import Submission.FeketeLim
import Submission.XTransfer
import Submission.DirSet
import Submission.ChebPower
import Submission.PolyaCore
import Submission.Step3
import Submission.DubininMap
import Submission.FeketeDecayOfLimsup

/-!
# SS1 -- Dubinin's Fekete inequality for the hedgehog (statement file)

The single remaining deep potential-theoretic intermediate of the E1 chain:
a hedgehog whose `s := |dirSet S|` spikes are all strictly shorter than
`4^(1/s)` has transfinite diameter `< 1` -- i.e. its Fekete numbers decay:

  (sharp limsup form, `dubinin_fekete_limsup`)
      limsup_n (feketeNumber (Submission.XTransfer.star S) (n+1))^(2/((n+1)·n))
          ≤ 4^(-1/s) · max_{w ∈ spikeEndpoints S} ‖w‖   (< 1 when the
          spikes are all < 4^(1/s));

  (decay form, equivalent via the limsup<1-is-eventually-geometric step +
  absorbing small n)
      ∃ ρ < 1, ∃ C, ∀ n ≥ 1: feketeNumber (Submission.XTransfer.star S) n ≤ C · ρ^(n(n−1)/2)
      (= `fekete_decay_of_short_spikes` in Submission/Dubinin.lean).

GEOMETRY (this file proves the elementary part):
* the hedgehog `star S = ⋃_{w ∈ spikeEndpoints S} [0, w]` (each `z ∈ S`
  contributes the two segments `[0,z²]`, `[0,z⁴]`; `spikeEndpoints S =
  {z², z⁴ : z ∈ S}`) -- `star_eq_biUnion_spikeEndpoints`;
* `star S` is compact (Submission.ChebPower.isCompact_star), so for
  `S.Nonempty` the Fekete numbers of `star S` are finite/nonnegative
  (`feketeNumber_star_nonneg`, via Submission.FeketeLim), and the
  `feketeSet` is bounded above;
* a bound on the maximal spike length (`maxSpikeLen`) from the short-spike
  hypothesis.

THE DEEP STATEMENT (`dubinin_fekete_limsup`): Dubinin's inequality for
hedgehogs -- the genuine potential-theory content (per-spike distribution
of Fekete points among the `s` spikes + a symmetrization/angular argument,
or Eremenko's conformal representation + the verified Konyagin-Lev circle
inequality).  NOT proved here; marked `sorry` (do not import until proved).

From `dubinin_fekete_limsup` the decay form follows (with the same
`ρ ∈ (4^(-1/s)·L, 1)`): record that as `fekete_decay_of_short_spikes` --
also `sorry` (assembly).
-/

noncomputable section

open scoped Real Polynomial Topology BigOperators

namespace Submission.SS1

set_option maxHeartbeats 0

open Submission.DirSet
open Submission.DirSet
open Submission.PolyaCore
open Filter

/-- The Vandermonde product of `n` points. -/
def vdm (x : ℕ → ℂ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range i, ‖x j - x i‖

/-- The set of Vandermonde products over `n`-point configurations in `K`. -/
def feketeSet (K : Set ℂ) (n : ℕ) : Set ℝ :=
  {d : ℝ | ∃ x : ℕ → ℂ, (∀ i : ℕ, i < n → x i ∈ K) ∧ d = vdm x n}

/-- **Fekete number.** -/
def feketeNumber (K : Set ℂ) (n : ℕ) : ℝ := sSup (feketeSet K n)

/-- Maximal spike length of the hedgehog over `S`. -/
def maxSpikeLen (S : Finset ℂ) : ℝ :=
  sSup {r : ℝ | ∃ w ∈ spikeEndpoints S, r = ‖w‖}

/-- The hedgehog is compact. -/
lemma isCompact_star (S : Finset ℂ) : IsCompact (Submission.XTransfer.star S) := by
  exact Submission.ChebPower.isCompact_star S

/-- The Fekete numbers of the hedgehog are nonnegative (for nonempty `S`). -/
lemma feketeNumber_star_nonneg (S : Finset ℂ) (hSne : S.Nonempty) (n : ℕ) :
    0 ≤ feketeNumber (Submission.XTransfer.star S) n := by
  have hKb : Bornology.IsBounded (Submission.XTransfer.star S) := (isCompact_star S).isBounded
  exact Submission.FeketeLim.feketeNumber_nonneg (K := Submission.XTransfer.star S)
    (⟨0, Submission.XTransfer.zero_mem_star hSne⟩) hKb n

/-- Short spikes bound the maximal spike length: if every endpoint has norm
`< L` and `spikeEndpoints S` is nonempty, then `maxSpikeLen S ≤ L`. -/
lemma maxSpikeLen_le_of_short {S : Finset ℂ} {L : ℝ}
    (hne : (spikeEndpoints S).Nonempty)
    (hshort : ∀ w ∈ spikeEndpoints S, ‖w‖ < L) : maxSpikeLen S ≤ L := by
  classical
  unfold maxSpikeLen
  refine csSup_le ?_ ?_
  · -- the set of spike norms is nonempty
    rcases hne with ⟨w, hw⟩
    exact ⟨‖w‖, w, hw, rfl⟩
  · intro r hr
    rcases hr with ⟨w, hw, rfl⟩
    exact le_of_lt (hshort w hw)

/-! ## Wiring helpers: translation between the duplicate Fekete-number
definitions and the star-lengthening geometry -/

/-- SS1's `feketeNumber` equals `FeketeLim`'s (identical definitions). -/
lemma feketeNumber_eq_FeketeLim (K : Set ℂ) (n : ℕ) :
    feketeNumber K n = Submission.FeketeLim.feketeNumber K n := by
  simp [feketeNumber, Submission.FeketeLim.feketeNumber, feketeSet,
    Submission.FeketeLim.feketeSet, vdm, Submission.FeketeLim.vdm]

/-- SS1's `feketeNumber` equals `DubininMap`'s (identical definitions). -/
lemma feketeNumber_eq_DubininMap (K : Set ℂ) (n : ℕ) :
    feketeNumber K n = Submission.DubininMap.feketeNumber K n := by
  simp [feketeNumber, Submission.DubininMap.feketeNumber, feketeSet,
    Submission.DubininMap.feketeSet, vdm, Submission.DubininMap.vdm]

/-- A nonempty direction set means nonempty spike endpoints. -/
lemma spikeEndpoints_nonempty_of_dirSet_card_pos (S : Finset ℂ)
    (hs : 0 < (dirSet S).card) : (spikeEndpoints S).Nonempty := by
  classical
  have hD : (dirSet S).Nonempty := Finset.card_pos.mp hs
  rcases hD with ⟨θ, hθ⟩
  rw [dirSet] at hθ
  exact Finset.image_nonempty.mp ⟨θ, hθ⟩

/-- Every element of `dirSet S` is an argument, hence lies in `(-π, π]`. -/
lemma dirSet_mem_Ioc (S : Finset ℂ) {θ : ℝ} (hθ : θ ∈ dirSet S) :
    θ ∈ Set.Ioc (-Real.pi) Real.pi := by
  classical
  rw [dirSet] at hθ
  rcases Finset.mem_image.mp hθ with ⟨c, hc, rfl⟩
  exact Complex.arg_mem_Ioc c

/-- The unit-direction map `θ ↦ exp(θ·I)` is injective on the direction set
(arguments in `(-π, π]`). -/
lemma dirUnit_injOn_dirSet (S : Finset ℂ) :
    Set.InjOn (fun θ : ℝ => Complex.exp (θ * Complex.I)) (dirSet S : Set ℝ) := by
  intro θ₁ hθ₁ θ₂ hθ₂ h
  have hIoc₁ : θ₁ ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    rcases dirSet_mem_Ioc S hθ₁ with ⟨hlo, hle⟩
    exact ⟨hlo, by linarith⟩
  have hIoc₂ : θ₂ ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    rcases dirSet_mem_Ioc S hθ₂ with ⟨hlo, hle⟩
    exact ⟨hlo, by linarith⟩
  have harg : (Complex.exp (θ₁ * Complex.I)).arg = (Complex.exp (θ₂ * Complex.I)).arg := by
    simpa using congrArg Complex.arg h
  rw [Complex.arg_exp_mul_I, Complex.arg_exp_mul_I] at harg
  have h₁ : (toIocMod Real.two_pi_pos (-Real.pi) θ₁) = θ₁ :=
    (toIocMod_eq_self Real.two_pi_pos (a := -Real.pi) (b := θ₁)).2 hIoc₁
  have h₂ : (toIocMod Real.two_pi_pos (-Real.pi) θ₂) = θ₂ :=
    (toIocMod_eq_self Real.two_pi_pos (a := -Real.pi) (b := θ₂)).2 hIoc₂
  simpa [h₁, h₂] using harg

/-- The cardinality of the unit-direction image equals the direction-set
cardinality. -/
lemma dirUnit_image_card (S : Finset ℂ) :
    (((dirSet S).image (fun θ : ℝ => Complex.exp (θ * Complex.I))).card) = (dirSet S).card := by
  classical
  exact Finset.card_image_of_injOn (dirUnit_injOn_dirSet S)

/-- The hedgehog `star S` lies in the unit-direction star of length
`maxSpikeLen S` (via the lengthened star). -/
lemma star_subset_dirStar_maxSpikeLen (S : Finset ℂ)
    (hne : (spikeEndpoints S).Nonempty) :
    Submission.XTransfer.star S ⊆
      Step3.dirStar ((dirSet S).image (fun θ : ℝ => Complex.exp (θ * Complex.I)))
        (maxSpikeLen S) := by
  intro X hX
  have hL : X ∈ DubininMap.starL S (maxSpikeLen S) :=
    DubininMap.star_subset_starL S hne hX
  rcases hL with ⟨θ, hθ, hseg⟩
  refine ⟨Complex.exp (θ * Complex.I), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨θ, hθ, rfl⟩
  · dsimp [DubininMap.dirUnit] at hseg
    exact hseg

/-- The unit-direction star is bounded by `L` in norm (same as the
lengthened star, which is bounded by `DubininMap.norm_le_of_mem_starL`). -/
lemma norm_le_of_mem_dirStar {S : Finset ℂ} {L : ℝ} (hL0 : 0 ≤ L) {X : ℂ}
    (hX : X ∈ Step3.dirStar ((dirSet S).image (fun θ : ℝ => Complex.exp (θ * Complex.I))) L) :
    ‖X‖ ≤ L := by
  rcases hX with ⟨w, hw, hseg⟩
  rcases Finset.mem_image.mp hw with ⟨θ, hθ, rfl⟩
  exact DubininMap.norm_le_of_mem_starL hL0 ⟨θ, hθ, hseg⟩

/-- The `dirStar` set over the unit directions of `S` contains `star S`
(both bounded: Fekete families of the bigger star are bounded above). -/
lemma feketeNumber_star_le_dirStar (S : Finset ℂ) (hne : (spikeEndpoints S).Nonempty)
    (n : ℕ) :
    feketeNumber (Submission.XTransfer.star S) n ≤
      feketeNumber (Step3.dirStar ((dirSet S).image (fun θ : ℝ => Complex.exp (θ * Complex.I)))
        (maxSpikeLen S)) n := by
  classical
  let L : ℝ := maxSpikeLen S
  let u : Finset ℂ := (dirSet S).image (fun θ : ℝ => Complex.exp (θ * Complex.I))
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact DubininMap.maxSpikeLen_nonneg hne
  have hsub : Submission.XTransfer.star S ⊆ Step3.dirStar u L := by
    dsimp [u, L]
    exact star_subset_dirStar_maxSpikeLen S hne
  -- smaller family nonempty: 0 ∈ star S (S nonempty)
  have hSne : S.Nonempty := by
    rcases hne with ⟨w, hw⟩
    rw [spikeEndpoints, Finset.mem_union] at hw
    rcases hw with hw | hw
    · rcases (Finset.mem_image.mp hw) with ⟨z, hz, _⟩
      exact ⟨z, hz⟩
    · rcases (Finset.mem_image.mp hw) with ⟨z, hz, _⟩
      exact ⟨z, hz⟩
  have hstarne : (Submission.XTransfer.star S).Nonempty :=
    ⟨0, Submission.XTransfer.zero_mem_star hSne⟩
  have hKne : (feketeSet (Submission.XTransfer.star S) n).Nonempty :=
    DubininMap.feketeSet_nonempty_of_nonempty hstarne n
  have hbdd : BddAbove (feketeSet (Step3.dirStar u L) n) :=
    DubininMap.feketeSet_bddAbove_of_norm_le (E := Step3.dirStar u L)
      (R := L) (n := n) (fun X hX => norm_le_of_mem_dirStar (S := S) (L := L) hL0 hX)
  rw [feketeNumber_eq_DubininMap, feketeNumber_eq_DubininMap]
  exact DubininMap.feketeNumber_mono (K := Submission.XTransfer.star S)
    (K' := Step3.dirStar u L) hsub n hKne hbdd



lemma maxSpikeLen_lt_of_all_lt (S : Finset ℂ) (hne : (spikeEndpoints S).Nonempty) {c : ℝ}
    (h : ∀ w ∈ spikeEndpoints S, ‖w‖ < c) : maxSpikeLen S < c := by
  classical
  unfold maxSpikeLen
  let A : Finset ℝ := (spikeEndpoints S).image (fun w : ℂ => ‖w‖)
  have hAeq : ({r : ℝ | ∃ w ∈ spikeEndpoints S, r = ‖w‖} : Set ℝ) = (A : Set ℝ) := by
    ext r
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
    · intro hr
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hr) with ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
  rw [hAeq]
  have hAne : A.Nonempty := Finset.image_nonempty.mpr hne
  have hmc : A.max' hAne < c := (Finset.max'_lt_iff A hAne).2 (by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨w, hw, rfl⟩
    exact h w hw)
  have hsup_le : sSup (A : Set ℝ) ≤ A.max' hAne := by
    refine csSup_le ?hne ?hle
    · exact ⟨A.max' hAne, Finset.mem_coe.mpr (Finset.max'_mem A hAne)⟩
    · intro r hr
      exact Finset.le_max' A r (Finset.mem_coe.mp hr)
  have hm_le_sup : A.max' hAne ≤ sSup (A : Set ℝ) :=
    le_csSup A.bddAbove (Finset.mem_coe.mpr (Finset.max'_mem A hAne))
  calc
    sSup (A : Set ℝ) = A.max' hAne := le_antisymm hsup_le hm_le_sup
    _ < c := hmc

/-- **Dubinin's Fekete inequality (DEEP, the potential-theory crux).**  The
limsup of the Fekete root numbers of the hedgehog is at most
`4^(-1/s) · maxSpikeLen S`. -/
theorem dubinin_fekete_limsup (S : Finset ℂ) (hs : 0 < (dirSet S).card) :
    Filter.limsup (fun n : ℕ =>
        (feketeNumber (Submission.XTransfer.star S) (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ))))
      Filter.atTop
      ≤ (4 : ℝ) ^ (-1 / ((dirSet S).card : ℝ)) * maxSpikeLen S := by
  classical
  let D : Finset ℝ := dirSet S
  let u : Finset ℂ := D.image (fun θ : ℝ => Complex.exp (θ * Complex.I))
  let L : ℝ := maxSpikeLen S
  have hne : (spikeEndpoints S).Nonempty := spikeEndpoints_nonempty_of_dirSet_card_pos S hs
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact DubininMap.maxSpikeLen_nonneg hne
  let f1 : ℕ → ℝ := fun n =>
    (feketeNumber (Submission.XTransfer.star S) (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ)))
  let f2 : ℕ → ℝ := fun n =>
    (Submission.FeketeLim.feketeNumber (Step3.dirStar u L) (n + 1)) ^
      (2 / (((n + 1 : ℝ)) * (n : ℝ)))
  have f1_nonneg : ∀ n : ℕ, 0 ≤ f1 n := by
    intro n
    dsimp [f1]
    exact Real.rpow_nonneg (by
      rw [feketeNumber_eq_FeketeLim]
      exact Submission.FeketeDecayOfLimsup.feketeNumber_nonneg_all
        (Submission.XTransfer.star S) (n + 1)) _
  have f1_le_f2 : ∀ n : ℕ, f1 n ≤ f2 n := by
    intro n
    have hb0 : 0 ≤ feketeNumber (Submission.XTransfer.star S) (n + 1) := by
      rw [feketeNumber_eq_FeketeLim]
      exact Submission.FeketeDecayOfLimsup.feketeNumber_nonneg_all
        (Submission.XTransfer.star S) (n + 1)
    have hle : feketeNumber (Submission.XTransfer.star S) (n + 1) ≤
        Submission.FeketeLim.feketeNumber (Step3.dirStar u L) (n + 1) := by
      calc
        feketeNumber (Submission.XTransfer.star S) (n + 1)
            = Submission.FeketeLim.feketeNumber (Submission.XTransfer.star S) (n + 1) := by
              rw [feketeNumber_eq_FeketeLim]
        _ ≤ Submission.FeketeLim.feketeNumber (Step3.dirStar u L) (n + 1) := by
              have h0 := feketeNumber_star_le_dirStar S hne (n + 1)
              simpa [u, L, feketeNumber_eq_FeketeLim] using h0
    have he0 : 0 ≤ (2 : ℝ) / (((n + 1 : ℝ)) * (n : ℝ)) := by
      by_cases hn : n = 0
      · subst n
        simp
      · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        positivity
    have hmain : (feketeNumber (Submission.XTransfer.star S) (n + 1)) ^
          (2 / (((n + 1 : ℝ)) * (n : ℝ))) ≤
        (Submission.FeketeLim.feketeNumber (Step3.dirStar u L) (n + 1)) ^
          (2 / (((n + 1 : ℝ)) * (n : ℝ))) := by
      exact Real.rpow_le_rpow hb0 hle he0
    simpa [f1, f2] using hmain
  -- f1 is cobounded below (terms nonnegative)
  have hcob : Filter.IsCoboundedUnder (fun x1 x2 : ℝ => x1 ≤ x2) Filter.atTop f1 := by
    unfold Filter.IsCoboundedUnder Filter.IsCobounded
    refine ⟨0, ?_⟩
    intro a ha
    rw [Filter.eventually_map] at ha
    rcases (Filter.eventually_atTop).1 ha with ⟨N, hN⟩
    exact le_trans (f1_nonneg N) (hN N (le_refl N))
  -- f2 is bounded above (the dirStar is bounded by L)
  have hbdd : Filter.IsBoundedUnder (fun x1 x2 : ℝ => x1 ≤ x2) Filter.atTop f2 := by
    unfold Filter.IsBoundedUnder Filter.IsBounded
    refine ⟨(max 1 (2 * L)) ^ 4, ?_⟩
    rw [Filter.eventually_map]
    apply Filter.Eventually.of_forall
    intro n
    dsimp [f2]
    have hsub : ∀ X : ℂ, X ∈ Step3.dirStar u L → ‖X‖ ≤ L := by
      intro X hX
      simpa [u] using norm_le_of_mem_dirStar (S := S) (L := L) hL0 hX
    have hbounded : Bornology.IsBounded (Step3.dirStar u L) := by
      rw [Metric.isBounded_iff_subset_closedBall (c := (0 : ℂ))]
      refine ⟨L, ?_⟩
      intro X hX
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact hsub X hX
    have hne2 : (Step3.dirStar u L).Nonempty := by
      have huD : u.Nonempty := by
        dsimp [u, D]
        exact (Finset.image_nonempty.mpr (Finset.card_pos.mp hs))
      rcases huD with ⟨w, hw⟩
      refine ⟨0, w, hw, ?_⟩
      exact left_mem_segment ℝ (0 : ℂ) ((L : ℂ) * w)
    exact Submission.FeketeLim.feketeRoot_bounded hne2 hbounded hL0 hsub n
  -- (2) limsup comparison
  have hlim1 : Filter.limsup f1 Filter.atTop ≤ Filter.limsup f2 Filter.atTop := by
    exact Filter.limsup_le_limsup (Filter.Eventually.of_forall f1_le_f2) hcob hbdd
  -- (3) sym_maximality on the unit directions
  have hu : ∀ w ∈ u, ‖w‖ = 1 := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨θ, hθ, rfl⟩
    exact Complex.norm_exp_ofReal_mul_I θ
  have hus : 1 ≤ u.card := by
    dsimp [u, D]
    rw [dirUnit_image_card S]
    exact Nat.succ_le_of_lt hs
  have hsym := Step3.sym_maximality u hu hus hL0
  have hlim2 : Filter.limsup f2 Filter.atTop ≤ (L : ℝ) * (4 : ℝ) ^ (-1 / (u.card : ℝ)) := by
    simpa [f2] using hsym
  -- (4) arithmetic match
  have huc : (u.card : ℝ) = ((dirSet S).card : ℝ) := by
    dsimp [u, D]
    rw [dirUnit_image_card S]
  have hrhs : (L : ℝ) * (4 : ℝ) ^ (-1 / (u.card : ℝ)) =
      (4 : ℝ) ^ (-1 / ((dirSet S).card : ℝ)) * maxSpikeLen S := by
    dsimp [L]
    rw [huc]
    ring_nf
  calc
    Filter.limsup (fun n : ℕ =>
        (feketeNumber (Submission.XTransfer.star S) (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ))))
        Filter.atTop
        = Filter.limsup f1 Filter.atTop := by rfl
    _ ≤ Filter.limsup f2 Filter.atTop := hlim1
    _ ≤ (L : ℝ) * (4 : ℝ) ^ (-1 / (u.card : ℝ)) := hlim2
    _ = (4 : ℝ) ^ (-1 / ((dirSet S).card : ℝ)) * maxSpikeLen S := hrhs
/-- **Decay form (assembly).**  Short spikes give geometric decay of the
Fekete numbers of the hedgehog.  (= `fekete_decay_of_short_spikes` in
Submission/Dubinin.lean; follows from `dubinin_fekete_limsup` since
`4^(-1/s)·maxSpikeLen < 1`.) -/
theorem fekete_decay_of_short_spikes (S : Finset ℂ) (hs : 0 < (dirSet S).card)
    (hshort : ∀ w ∈ spikeEndpoints S,
      ‖w‖ < (4 : ℝ) ^ (1 / ((dirSet S).card : ℝ))) :
    ∃ ρ C : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ 0 ≤ C ∧
      ∀ n : ℕ, 1 ≤ n →
        feketeNumber (Submission.XTransfer.star S) n ≤ C * ρ ^ (n * (n - 1) / 2) := by
  classical
  let s : ℝ := ((dirSet S).card : ℝ)
  let c : ℝ := (4 : ℝ) ^ (1 / s)
  have hne : (spikeEndpoints S).Nonempty := spikeEndpoints_nonempty_of_dirSet_card_pos S hs
  have hc_pos : 0 < c := by
    dsimp [c, s]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) _
  have hLlt : maxSpikeLen S < c := by
    dsimp [c, s]
    exact maxSpikeLen_lt_of_all_lt S hne hshort
  have hL0 : 0 ≤ maxSpikeLen S := DubininMap.maxSpikeLen_nonneg hne
  let ρ0 : ℝ := (4 : ℝ) ^ (-1 / s) * maxSpikeLen S
  have hfour : (0 : ℝ) < 4 := by norm_num
  have hρ0_ge0 : 0 ≤ ρ0 := by
    dsimp [ρ0]
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hfour) _) hL0
  have hρ0_lt1 : ρ0 < 1 := by
    dsimp [ρ0]
    have hmul : (4 : ℝ) ^ (-1 / s) * maxSpikeLen S < (4 : ℝ) ^ (-1 / s) * c := by
      exact mul_lt_mul_of_pos_left hLlt (Real.rpow_pos_of_pos hfour _)
    have hid : (4 : ℝ) ^ (-1 / s) * (4 : ℝ) ^ (1 / s) = 1 := by
      rw [← Real.rpow_add hfour]
      have hsR : s ≠ 0 := by
        dsimp [s]
        exact_mod_cast (ne_of_gt hs)
      have hexp : -1 / s + 1 / s = 0 := by
        field_simp [hsR]
        ring
      rw [hexp, Real.rpow_zero]
    calc
      (4 : ℝ) ^ (-1 / s) * maxSpikeLen S < (4 : ℝ) ^ (-1 / s) * c := hmul
      _ = (4 : ℝ) ^ (-1 / s) * (4 : ℝ) ^ (1 / s) := by simp [c]
      _ = 1 := hid
  have hlim0 : Filter.limsup (fun n : ℕ =>
        (Submission.FeketeLim.feketeNumber (Submission.XTransfer.star S) (n + 1)) ^
          (2 / (((n + 1 : ℝ)) * (n : ℝ)))) Filter.atTop ≤ ρ0 := by
    have hdl := dubinin_fekete_limsup S hs
    simpa [ρ0, s, feketeNumber_eq_FeketeLim] using hdl
  rcases (Submission.FeketeDecayOfLimsup.fekete_decay_of_root_limsup_le
      (K := Submission.XTransfer.star S) (ρ0 := ρ0) hρ0_ge0 hρ0_lt1 hlim0)
    with ⟨ρ, C, hρ0, hρ1, hC0, hmain⟩
  refine ⟨ρ, C, hρ0, hρ1, hC0, ?_⟩
  intro n hn
  have hb := hmain n hn
  simpa [feketeNumber_eq_FeketeLim] using hb


