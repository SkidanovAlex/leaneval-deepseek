/-
# `Work.SeedCertRay.Final` — the ray-chain landing theorem

The assembly of the whole area: the emitted interval certificate (`DataAll`, `Num`, `Chk`,
`Levels`) proves that the ten rays of the `α₁`-orbit enter the repelling petal `Re w < -4` of the
parabolic point `z₁` at level `K = 70` and stay there; the tail induction
(`landsN_of_petal_of_isDynBottcher`) then converts this into the landing of the rays `α₁` and
`α₂` at `z₁`.

Main export: `Work.SeedCertRay.landsAt_alphas_data`, which proves
`Work.Landing.landsAt c α₁ z₁ ∧ Work.Landing.landsAt c α₂ z₁` from

* the dynamical data `hN : Work.EL.DynB c φ`, `hφ : IsDynBottcher c φ`;
* `hc : c ∈ Mandelbar`, `‖c‖ ≤ 2` (the far-field estimate), `hcX : Xb.mem c` (the parameter box
  of the certificate, `c_b` to within `2 ^ -30`);
* the certified parabolic data `z₁ ∈ Zb`, `A ∈ Ab` (boxes of half-width `2 ^ -20`),
  `(T_c)^[5] z₁ = z₁`;
* the petal data `δ`, `ρ₁` and the two petal facts `hP1`/`hP2` (supplied by `SeedCertNum`'s
  `petal_P1`/`petal_P2`).
-/
import Mathlib
import Submission.Work.SeedCertRay.Q
import Submission.Work.SeedCertRay.Levels
import Submission.Work.SeedCertRay.chain_sound_sets_range
import Submission.Work.SeedCertRay.lvl0_cover2
import Submission.Work.SeedCertRay.dir_bound
import Submission.Work.SeedCertRay.landsN_of_petal_of_isDynBottcher
import Submission.Work.SeedCertRay.landsN_alpha2_of_landsN_alpha1
import Submission.Work.SeedCertRay.landsAt_alphas_of_disks
import Submission.Work.SeedCertRay.T_iterate_alpha1

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.SeedCertRay

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Set

/-! ## The level and angle sequences of the chain -/

/-- The levels of the certificate: `ρ 0 = 256`, `ρ (k+1) = √(ρ k)`. -/
def rhoL : ℕ → ℝ
  | 0 => 4096
  | (k + 1) => Real.sqrt (rhoL k)

theorem rhoL_pos (k : ℕ) : 0 < rhoL k := by
  induction k with
  | zero => norm_num [rhoL]
  | succ k ih => rw [rhoL]; exact Real.sqrt_pos.mpr ih

theorem rhoL_gt_one : ∀ k : ℕ, 1 < rhoL k := by
  intro k
  induction k with
  | zero => norm_num [rhoL]
  | succ k ih =>
      rw [rhoL]
      exact Real.lt_sqrt_of_sq_lt (by simpa using ih)

theorem rhoL_one_lt (k : ℕ) : 1 < rhoL (k + 1) := rhoL_gt_one (k + 1)

theorem rhoL_sq (k : ℕ) : rhoL (k + 1) ^ 2 = rhoL k := by
  rw [rhoL, Real.sq_sqrt (le_of_lt (rhoL_pos k))]

@[simp] theorem rhoL_zero : rhoL 0 = 4096 := rfl

@[simp] theorem rhoL_one : rhoL 1 = 64 := by norm_num [rhoL]

theorem rhoL_spec : ∀ k, 1 < rhoL (k + 1) ∧ rhoL (k + 1) ^ 2 = rhoL k :=
  fun k => ⟨rhoL_one_lt k, rhoL_sq k⟩

/-- The angles of the chain: `θ j = T^[j] α₁`. -/
def thL (j : ℕ) : ℝ := (Work.EL.T^[j]) Work.EL.alpha1

@[simp] theorem thL_zero : thL 0 = Work.EL.alpha1 := rfl

theorem thL_succ (j : ℕ) : thL (j + 1) = Work.EL.T (thL j) := by
  simp [thL, Function.iterate_succ_apply']

theorem thL_add_ten (j : ℕ) : thL (j + 10) = thL j := by
  have h : thL (j + 10) = (Work.EL.T^[j]) ((Work.EL.T^[10]) Work.EL.alpha1) := by
    rw [thL, Function.iterate_add_apply]
  rw [h, T_iterate_alpha1]; rfl

theorem thL_mod (j : ℕ) : thL j = thL (j % 10) := by
  have hmain : ∀ q : ℕ, thL (j % 10 + 10 * q) = thL (j % 10) := by
    intro q
    induction q with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ, ← add_assoc, thL_add_ten]; exact ih
  conv_lhs => rw [← Nat.mod_add_div j 10]
  exact hmain (j / 10)

/-! ## The assembly -/

theorem landsAt_alphas_data {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hc : c ∈ Mandelbar) (hc2 : ‖c‖ ≤ 2)
    (hcX : Xb.mem c) (z₁ A : ℂ) (hz1 : Zb.mem z₁) (hA : Ab.mem A)
    (hg : (Tantibar c)^[5] z₁ = z₁) (δ ρ₁ : ℝ) (hρ₁ : 0 < ρ₁) (hδ : 0 < δ) (hAne : A ≠ 0)
    (hRQ : 1 ≤ 4 * ‖A‖ * ρ₁)
    (hP1 : ∀ z : ℂ, ‖z - z₁‖ = ρ₁ → Work.EL.F c z ∉ Petal z₁ A 4)
    (hP2 : ∀ z : ℂ, ‖z - z₁‖ ≤ ρ₁ → Work.EL.F c z ∈ Petal z₁ A 4 →
      z ∈ Petal z₁ A 4 ∧ (fatou z₁ A z).re ≤ (fatou z₁ A (Work.EL.F c z)).re - δ) :
    Work.Landing.landsAt c Work.EL.alpha1 z₁ ∧ Work.Landing.landsAt c Work.EL.alpha2 z₁ := by
  -- ### (D1): every preimage step is certified
  have hD1 : ∀ k, k ≤ 80 → ∀ j, ∀ u : ℂ,
      Tantibar c u ∈ diskUnion (Dd k (j + 1)) →
        u ∈ diskUnion (Dd (k + 1) j) ∨ -u ∈ diskUnion (Dd (k + 1) j) := by
    intro k hk j u hu
    simp only [mem_diskUnion] at hu ⊢
    obtain ⟨i, hi⟩ := hu
    rcases hD1At k hk j i (Tantibar c u) c u hi hcX rfl with h | h
    · exact Or.inl ⟨i, h⟩
    · exact Or.inr ⟨i, h⟩
  -- ### (D2): the two radial separations
  have hD2 : ∀ k, k ≤ 80 → ∀ j, IsClosed (diskUnion (Dd (k + 1) j)) ∧
      Disjoint (diskUnion (Dd (k + 1) j)) (-diskUnion (Dd (k + 1) j)) ∧
      Disjoint (diskUnion (Dd k j)) (-diskUnion (Dd (k + 1) j)) := by
    intro k hk j
    refine ⟨isClosed_diskUnion _, ?_, ?_⟩
    · exact disjoint_neg_of_halfplane (diskUnion_subset_halfplane (fun i => (hHPAt k hk j).1 i))
        (diskUnion_subset_halfplane (fun i => (hHPAt k hk j).1 i))
    · exact disjoint_neg_of_halfplane (diskUnion_subset_halfplane (fun i => (hHPAt k hk j).2 i))
        (diskUnion_subset_halfplane (fun i => (hHPAt k hk j).1 i))
  -- ### (D0): the far-field cover of the level-0 pieces
  have hD0 : ∀ j, seg hN (thL j) (rhoL 1) (rhoL 0) ⊆ diskUnion (Dd 0 j) := by
    intro j
    have hlt : j % 10 < 10 := Nat.mod_lt j (by norm_num)
    have hd : ‖Work.Landing.rayDirection ((Work.EL.T^[j % 10]) Work.EL.alpha1)
        - qdirC ((j % 10) % 10)‖ ≤ 1 / 10000 := by
      simpa only [Nat.mod_eq_of_lt hlt] using dir_bound (j % 10) hlt
    have h := lvl0_cover2 hN hφ hc hc2 (j % 10) hlt hd
    have hDj : Dd 0 j = Dd 0 (j % 10) := funext (fun i => Dd_mod 0 j i)
    rw [hDj, thL_mod j]
    simpa only [rhoL_one, rhoL_zero, thL] using h
  -- ### the chain
  have hchain : ∀ k, k ≤ 81 → ∀ j, seg hN (thL j) (rhoL (k + 1)) (rhoL k)
      ⊆ diskUnion (Dd k j) :=
    chain_sound_sets_range hN hφ thL thL_succ rhoL rhoL_spec
      (fun k j => diskUnion (Dd k j)) 80 hD0 hD1 hD2
  have hC : ∀ k, k ≤ 80 → seg hN Work.EL.alpha1 (rhoL (k + 1)) (rhoL k)
      ⊆ diskUnion (Dd k 0) := by
    intro k hk
    have h := hchain k (by omega) 0
    rwa [thL_zero] at h
  -- ### (D3): the petal entry
  have hQ : ∀ k, 71 ≤ k → k ≤ 80 → diskUnion (Dd k 0) ⊆ Petal z₁ A 4 :=
    fun k h1 h2 => hQAt k h1 h2 z₁ A hz1 hA
  -- ### the tail induction
  have h₁ : Work.EL.LandsN hN Work.EL.alpha1 z₁ :=
    landsN_of_petal_of_isDynBottcher hN hφ z₁ A 4 δ ρ₁ rhoL 71 rhoL_spec T_iterate_alpha1
      (fun k => diskUnion (Dd k 0)) hC hQ hρ₁ hδ hAne hRQ hP1 hP2
  have h₂ : Work.EL.LandsN hN Work.EL.alpha2 z₁ :=
    landsN_alpha2_of_landsN_alpha1 hN hφ hg h₁
  exact ⟨(Work.ELTop.landsN_iff_landsAt hN hφ Work.EL.alpha1 z₁).mp h₁,
    (Work.ELTop.landsN_iff_landsAt hN hφ Work.EL.alpha2 z₁).mp h₂⟩

end Work.SeedCertRay
