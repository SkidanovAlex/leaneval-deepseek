import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Diag
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLContract.Lemmas.mkX_mul
import Submission.Work.EKLContract.Lemmas.mkX_one_short
import Submission.Work.EKLComp.tau_algebra
import Submission.Work.EKLComp.thick_lattice_short_basis
import Submission.Work.EKLComp.thick_inj_given_short
import Submission.Work.EKLComp.V_unipotent_step
import Submission.Work.EKLComp.sep_at_critical_time
import Submission.Work.EKLComp.critical_time
import Submission.Work.EKLComp.subsquare_extract
import Submission.Work.EKLComp.dimH_zero_of_separated

/-!
# C1b: box__thick_lattice_short_basis dimension of `tau ⁻¹' Drho ρ` via separated sets

This file proves `Work.EKLContract.P_BoxDim`, i.e. for `ρ > 0`

  `¬ PosEnt a0 (Drho ρ) → dimH (tau ⁻¹' Drho ρ) = 0`.

The proof follows EKL, *Box dimension and topological entropy* (§8, Lemma 8.2 / Prop. 8.3) and the
Pisa notes §12:

* `key_sq` : on each half-open unit square `Qsq m` of `ℝ²`, the counting condition of
  `dimH_zero_of_separated` holds.  A large `ε₀ e^{-3(N-1)}`-separated set inside one unit square is
  cut by a `⌈2/ε₀⌉²` grid (`subsquare_extract`) into one sub-collection `G` of diameter `≤ ε₀`;
  `sep_at_critical_time` (the critical-time form of EKL Lemma 8.2, using the uniform separation of
  thick lattices `thick_inj_given_short` and the elementary perturbation estimate
  `V_unipotent_step`) shows that `tau '' G` is `(N, ε₀)`-separated for `a₀`, so `¬ PosEnt` forces
  the cardinality bound.  The critical time is supplied by `critical_time`.
* `boxdim_core` : `ℝ²` is covered by the countably many unit squares and `dimH_iUnion` finishes.

The heavy geometric input (Mahler compactness, i.e. that a unimodular lattice with `λ₁ ≥ ρ` has a
basis of bounded vectors) is `thick_lattice_short_basis`, and the passage from it to the uniform
separation of conjugates of `Γ₃` is `thick_inj_given_short`.
-/

namespace Work.EKLComp

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

/-- The half-open unit square with index `m`. -/
def Qsq (m : ℤ × ℤ) : Set (ℝ × ℝ) :=
  {x | (m.1 : ℝ) ≤ x.1 ∧ x.1 < (m.1 : ℝ) + 1 ∧ (m.2 : ℝ) ≤ x.2 ∧ x.2 < (m.2 : ℝ) + 1}

theorem mem_Qsq (x : ℝ × ℝ) : ∃ m : ℤ × ℤ, x ∈ Qsq m := by
  refine ⟨(⌊x.1⌋, ⌊x.2⌋), ?_, ?_, ?_, ?_⟩
  · exact Int.floor_le x.1
  · exact Int.lt_floor_add_one x.1
  · exact Int.floor_le x.2
  · exact Int.lt_floor_add_one x.2

theorem dist_prod (p q : ℝ × ℝ) : dist p q = max |p.1 - q.1| |p.2 - q.2| := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]

/-- The number of subsquares used in the pigeonhole. -/
noncomputable def Ksq (ε₀ : ℝ) : ℕ := (Nat.ceil (2 / ε₀)) ^ 2

/-- The per-unit-square reduction, with all ingredients as hypotheses. -/
theorem key_sq (ρ ε₀ δ : ℝ) (hρ : 0 < ρ) (hδpos : 0 < δ) (hε₀pos : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hε₀lt : ε₀ < 1)
    (tauiff : ∀ p p' : ℝ × ℝ, tau p = tau p' ↔
      (∃ k l : ℤ, p.1 - p'.1 = (k : ℝ) ∧ p.2 - p'.2 = (l : ℝ)))
    (hε₀δ : 2600 * ε₀ ≤ δ) (hno : ¬ PosEnt a0 (Drho ρ))
    (hinj : ∀ s : SL3, (∀ m : Fin 3 → ℤ, m ≠ 0 →
        ρ ≤ ‖Matrix.mulVec (toMat s) (fun j => (m j : ℝ))‖) →
      ∀ γ : SL3, γ ∈ Γ3 → γ ≠ 1 → ¬ (s * γ * s⁻¹ ∈ V δ))
    (hsep : ∀ (p p' : ℝ × ℝ), tau p ∈ Drho ρ → ∀ (n : ℕ), 1 ≤ n →
      (ε₀ ≤ |Real.exp (3 * (n : ℝ)) * (p'.1 - p.1)| ∨
        ε₀ ≤ |Real.exp (3 * (n : ℝ)) * (p'.2 - p.2)|) →
      |Real.exp (3 * (n : ℝ)) * (p'.1 - p.1)| ≤ Real.exp 3 * ε₀ →
      |Real.exp (3 * (n : ℝ)) * (p'.2 - p.2)| ≤ Real.exp 3 * ε₀ →
      ¬ CloseBy ε₀ (a0 ^ n • tau p) (a0 ^ n • tau p'))
    (hcrit : ∀ (d : ℝ), 0 < d → d ≤ ε₀ → ∀ N : ℕ, 2 ≤ N →
      ε₀ * Real.exp (-(3 * ((N : ℝ) - 1))) ≤ d →
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ N - 1 ∧ ε₀ ≤ Real.exp (3 * (n : ℝ)) * d ∧
        Real.exp (3 * (n : ℝ)) * d ≤ Real.exp 3 * ε₀)
    (hsub : ∀ F : Finset (ℝ × ℝ), (∀ x ∈ F, 0 ≤ x.1 ∧ x.1 < 1 ∧ 0 ≤ x.2 ∧ x.2 < 1) →
      ∃ G : Finset (ℝ × ℝ), G ⊆ F ∧ (∀ x ∈ G, ∀ y ∈ G, dist x y ≤ ε₀) ∧
        F.card ≤ (Nat.ceil (2 / ε₀)) ^ 2 * G.card)
    (hcount : ∀ S : Set (ℝ × ℝ),
      (∀ b : ℝ, 0 < b → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ F : Finset (ℝ × ℝ),
        (F : Set (ℝ × ℝ)) ⊆ S →
        (∀ x ∈ F, ∀ y ∈ F, x ≠ y → (ε₀ * Real.exp 3) * Real.exp (-(3 * (N : ℝ))) ≤ dist x y) →
        (F.card : ℝ) < Real.exp (3 * b * (N : ℝ))) →
      dimH S = 0)
    (m : ℤ × ℤ) :
    dimH (tau ⁻¹' Drho ρ ∩ Qsq m) = 0 := by
  classical
  apply hcount (tau ⁻¹' Drho ρ ∩ Qsq m)
  intro b hb
  by_contra hcon
  push_neg at hcon
  have hlarge : ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧ ∃ F : Finset (ℝ × ℝ),
      (F : Set (ℝ × ℝ)) ⊆ tau ⁻¹' Drho ρ ∩ Qsq m ∧
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → (ε₀ * Real.exp 3) * Real.exp (-(3 * (N : ℝ))) ≤ dist x y) ∧
      Real.exp (3 * b * (N : ℝ)) ≤ (F.card : ℝ) := by
    intro N₀
    obtain ⟨N, hN, F, hF1, hF2, hF3⟩ := hcon N₀
    exact ⟨N, hN, F, hF1, hF2, hF3⟩
  -- a threshold beyond which `e^{bN}` dominates the number of subsquares
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      ((Ksq ε₀) : ℝ) ≤ Real.exp (b * (N : ℝ)) := by
    have hT : Tendsto (fun N : ℕ => Real.exp (b * (N : ℝ))) atTop atTop :=
      Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop hb tendsto_natCast_atTop_atTop)
    obtain ⟨N₁, hN₁⟩ := (hT.eventually_gt_atTop ((Ksq ε₀) : ℝ)).exists
    exact ⟨N₁, fun N hN => le_trans (le_of_lt hN₁)
      (Real.exp_le_exp.mpr (by
        have : (N₁ : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hN
        nlinarith [le_of_lt hb]))⟩
  apply hno
  refine ⟨ε₀, hε₀pos, 2 * b, by positivity, fun N₀ => ?_⟩
  obtain ⟨N, hN, F, hFsub, hFsep, hFcard⟩ := hlarge (max (max N₀ 2) N₁)
  have hN2 : 2 ≤ N := le_trans (le_trans (le_max_right N₀ 2) (le_max_left (max N₀ 2) N₁)) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_max_right _ _) hN
  have hNN₀ : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  -- translate the unit square to `[0,1)²` and extract a small-diameter sub-collection
  set T : ℝ × ℝ → ℝ × ℝ := fun x => (x.1 - (m.1 : ℝ), x.2 - (m.2 : ℝ)) with hT
  have hTinj : Function.Injective T := by
    intro a c hac
    have h1 : a.1 - (m.1 : ℝ) = c.1 - (m.1 : ℝ) := congrArg Prod.fst hac
    have h2 : a.2 - (m.2 : ℝ) = c.2 - (m.2 : ℝ) := congrArg Prod.snd hac
    exact Prod.ext (by linarith) (by linarith)
  set F' : Finset (ℝ × ℝ) := F.image T with hF'
  have hF'card : F'.card = F.card := Finset.card_image_of_injective F hTinj
  have hF'box : ∀ x ∈ F', 0 ≤ x.1 ∧ x.1 < 1 ∧ 0 ≤ x.2 ∧ x.2 < 1 := by
    intro x hx
    obtain ⟨y, hyF, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨h1a, h1b, h2a, h2b⟩ := (hFsub hyF).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp [T]; linarith
    · dsimp [T]; linarith
    · dsimp [T]; linarith
    · dsimp [T]; linarith
  obtain ⟨G', hG'sub, hG'diam, hG'card⟩ := hsub F' hF'box
  set T' : ℝ × ℝ → ℝ × ℝ := fun x => (x.1 + (m.1 : ℝ), x.2 + (m.2 : ℝ)) with hT'
  have hT'inj : Function.Injective T' := by
    intro a c hac
    have h1 : a.1 + (m.1 : ℝ) = c.1 + (m.1 : ℝ) := congrArg Prod.fst hac
    have h2 : a.2 + (m.2 : ℝ) = c.2 + (m.2 : ℝ) := congrArg Prod.snd hac
    exact Prod.ext (by linarith) (by linarith)
  set G : Finset (ℝ × ℝ) := G'.image T' with hG
  have hGsub : G ⊆ F := by
    intro x hx
    obtain ⟨z, hzG', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y, hyF, hyz⟩ := Finset.mem_image.mp (hG'sub hzG')
    have hzy : T' z = y := by
      rw [← hyz]
      ext <;> simp only [T, T'] <;> ring
    rw [hzy]
    exact hyF
  have hGcard : G.card = G'.card := Finset.card_image_of_injective G' hT'inj
  have hGdiam : ∀ x ∈ G, ∀ y ∈ G, dist x y ≤ ε₀ := by
    intro x hx y hy
    obtain ⟨a, haG', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hbG', rfl⟩ := Finset.mem_image.mp hy
    have hab := hG'diam a haG' b hbG'
    rw [dist_prod] at hab ⊢
    have e1 : |(a.1 + (m.1 : ℝ)) - (b.1 + (m.1 : ℝ))| = |a.1 - b.1| := by ring_nf
    have e2 : |(a.2 + (m.2 : ℝ)) - (b.2 + (m.2 : ℝ))| = |a.2 - b.2| := by ring_nf
    rw [e1, e2]
    exact hab
  -- the cardinality transfer
  have hKpos : (0 : ℝ) < ((Ksq ε₀) : ℝ) := by
    have h0 : 0 < Ksq ε₀ := by
      rw [Ksq]; exact pow_pos (Nat.ceil_pos.mpr (by positivity)) 2
    exact_mod_cast h0
  have hFK : (F.card : ℝ) ≤ ((Ksq ε₀) : ℝ) * (G.card : ℝ) := by
    have h := hG'card
    rw [hF'card, ← hGcard] at h
    exact_mod_cast h
  have hKle : ((Ksq ε₀) : ℝ) ≤ Real.exp (b * (N : ℝ)) := hN₁ N hNN₁
  have hGbig : Real.exp (2 * b * (N : ℝ)) ≤ (G.card : ℝ) := by
    have hstep : Real.exp (2 * b * (N : ℝ)) * ((Ksq ε₀) : ℝ)
        ≤ (G.card : ℝ) * ((Ksq ε₀) : ℝ) := by
      calc Real.exp (2 * b * (N : ℝ)) * ((Ksq ε₀) : ℝ)
          ≤ Real.exp (2 * b * (N : ℝ)) * Real.exp (b * (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hKle (le_of_lt (Real.exp_pos _))
        _ = Real.exp (3 * b * (N : ℝ)) := by
            rw [← Real.exp_add]; congr 1; ring
        _ ≤ (F.card : ℝ) := hFcard
        _ ≤ (G.card : ℝ) * ((Ksq ε₀) : ℝ) := by linarith [hFK]
    exact le_of_mul_le_mul_right hstep hKpos
  -- the entropy witness
  refine ⟨N, hNN₀, G.image tau, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, hpG, rfl⟩ := Finset.mem_image.mp hx
    exact (hFsub (hGsub hpG)).1
  · intro x hx y hy hxy
    obtain ⟨p, hpG, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨p', hp'G, rfl⟩ := Finset.mem_image.mp hy
    have hpp' : p ≠ p' := fun h => hxy (by rw [h])
    have hdiam : dist p p' ≤ ε₀ := hGdiam p hpG p' hp'G
    have hsep' : (ε₀ * Real.exp 3) * Real.exp (-(3 * (N : ℝ))) ≤ dist p p' :=
      hFsep p (hGsub hpG) p' (hGsub hp'G) hpp'
    have hpos : 0 < dist p p' := dist_pos.mpr hpp'
    have hsep'' : ε₀ * Real.exp (-(3 * ((N : ℝ) - 1))) ≤ dist p p' := by
      have : Real.exp (-(3 * ((N : ℝ) - 1))) = Real.exp 3 * Real.exp (-(3 * (N : ℝ))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [this]
      linarith [hsep']
    obtain ⟨n, hn1, hnN, hbig, hup⟩ := hcrit (dist p p') hpos hdiam N hN2 hsep''
    refine ⟨n, ?_, ?_⟩
    · omega
    · have hd := dist_prod p p'
      have hbig' : ε₀ ≤ |Real.exp (3 * (n : ℝ)) * (p'.1 - p.1)| ∨
          ε₀ ≤ |Real.exp (3 * (n : ℝ)) * (p'.2 - p.2)| := by
        have hd' : dist p p' = max |p'.1 - p.1| |p'.2 - p.2| := by
          rw [dist_comm, dist_prod]
        rw [hd'] at hbig
        by_cases hc : |p'.1 - p.1| ≤ |p'.2 - p.2|
        · right
          rw [max_eq_right hc] at hbig
          simpa only [abs_mul, abs_of_pos (Real.exp_pos _)] using hbig
        · left
          push Not at hc
          rw [max_eq_left (le_of_lt hc)] at hbig
          simpa only [abs_mul, abs_of_pos (Real.exp_pos _)] using hbig
      have h1 : |Real.exp (3 * (n : ℝ)) * (p'.1 - p.1)| ≤ Real.exp 3 * ε₀ := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        calc Real.exp (3 * (n : ℝ)) * |p'.1 - p.1|
            ≤ Real.exp (3 * (n : ℝ)) * dist p p' := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
              rw [hd, abs_sub_comm p'.1 p.1]; exact le_max_left _ _
          _ ≤ Real.exp 3 * ε₀ := hup
      have h2 : |Real.exp (3 * (n : ℝ)) * (p'.2 - p.2)| ≤ Real.exp 3 * ε₀ := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        calc Real.exp (3 * (n : ℝ)) * |p'.2 - p.2|
            ≤ Real.exp (3 * (n : ℝ)) * dist p p' := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
              rw [hd, abs_sub_comm p'.2 p.2]; exact le_max_right _ _
          _ ≤ Real.exp 3 * ε₀ := hup
      exact hsep p p' (hFsub (hGsub hpG)).1 n hn1 hbig' h1 h2
  · have hcard_image : (G.image tau).card = G.card := by
      rw [Finset.card_image_iff]
      intro p hpG p' hp'G htau
      obtain ⟨k, l, hk, hl⟩ := (tauiff p p').mp htau
      have hdist := hGdiam p hpG p' hp'G
      have h1 : k = 0 := by
        refine Work.EKLContract.Lemmas.int_eq_zero_of_abs_cast_lt_one ?_
        have hle : |(k : ℝ)| ≤ ε₀ := by
          rw [← hk]
          rw [dist_prod] at hdist
          exact le_trans (le_max_left _ _) hdist
        linarith [hε₀lt]
      have h2 : l = 0 := by
        refine Work.EKLContract.Lemmas.int_eq_zero_of_abs_cast_lt_one ?_
        have hle : |(l : ℝ)| ≤ ε₀ := by
          rw [← hl]
          rw [dist_prod] at hdist
          exact le_trans (le_max_right _ _) hdist
        linarith [hε₀lt]
      refine Prod.ext ?_ ?_
      · have hkk := hk
        rw [h1] at hkk
        exact sub_eq_zero.mp (by simpa using hkk)
      · have hll := hl
        rw [h2] at hll
        exact sub_eq_zero.mp (by simpa using hll)
    rw [hcard_image]
    exact hGbig

/-- The final assembly: choose `ε₀`, cover by unit squares, conclude. -/
theorem boxdim_core (ρ : ℝ) (hρ : 0 < ρ) (hno : ¬ PosEnt a0 (Drho ρ))
    (δ : ℝ) (hδpos : 0 < δ)
    (tauiff : ∀ p p' : ℝ × ℝ, tau p = tau p' ↔
      (∃ k l : ℤ, p.1 - p'.1 = (k : ℝ) ∧ p.2 - p'.2 = (l : ℝ)))
    (hinj : ∀ s : SL3, (∀ m : Fin 3 → ℤ, m ≠ 0 →
        ρ ≤ ‖Matrix.mulVec (toMat s) (fun j => (m j : ℝ))‖) →
      ∀ γ : SL3, γ ∈ Γ3 → γ ≠ 1 → ¬ (s * γ * s⁻¹ ∈ V δ))
    (hsep : ∀ (ε₀ : ℝ), 0 < ε₀ → ε₀ ≤ 1 → 2600 * ε₀ ≤ δ →
      ∀ (p p' : ℝ × ℝ), tau p ∈ Drho ρ → ∀ (n : ℕ), 1 ≤ n →
      (ε₀ ≤ |Real.exp (3 * (n : ℝ)) * (p'.1 - p.1)| ∨
        ε₀ ≤ |Real.exp (3 * (n : ℝ)) * (p'.2 - p.2)|) →
      |Real.exp (3 * (n : ℝ)) * (p'.1 - p.1)| ≤ Real.exp 3 * ε₀ →
      |Real.exp (3 * (n : ℝ)) * (p'.2 - p.2)| ≤ Real.exp 3 * ε₀ →
      ¬ CloseBy ε₀ (a0 ^ n • tau p) (a0 ^ n • tau p'))
    (hcrit : ∀ (ε₀ : ℝ), 0 < ε₀ → ∀ (d : ℝ), 0 < d → d ≤ ε₀ → ∀ N : ℕ, 2 ≤ N →
      ε₀ * Real.exp (-(3 * ((N : ℝ) - 1))) ≤ d →
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ N - 1 ∧ ε₀ ≤ Real.exp (3 * (n : ℝ)) * d ∧
        Real.exp (3 * (n : ℝ)) * d ≤ Real.exp 3 * ε₀)
    (hsub : ∀ (ε₀ : ℝ), 0 < ε₀ → ∀ F : Finset (ℝ × ℝ),
      (∀ x ∈ F, 0 ≤ x.1 ∧ x.1 < 1 ∧ 0 ≤ x.2 ∧ x.2 < 1) →
      ∃ G : Finset (ℝ × ℝ), G ⊆ F ∧ (∀ x ∈ G, ∀ y ∈ G, dist x y ≤ ε₀) ∧
        F.card ≤ (Nat.ceil (2 / ε₀)) ^ 2 * G.card)
    (hcount : ∀ (ε₀ : ℝ), 0 < ε₀ → ∀ S : Set (ℝ × ℝ),
      (∀ b : ℝ, 0 < b → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ F : Finset (ℝ × ℝ),
        (F : Set (ℝ × ℝ)) ⊆ S →
        (∀ x ∈ F, ∀ y ∈ F, x ≠ y → (ε₀ * Real.exp 3) * Real.exp (-(3 * (N : ℝ))) ≤ dist x y) →
        (F.card : ℝ) < Real.exp (3 * b * (N : ℝ))) →
      dimH S = 0) :
    dimH (tau ⁻¹' Drho ρ) = 0 := by
  set ε₀ : ℝ := min (1 / 2) (δ / 5200) with hε₀def
  have hε₀pos : 0 < ε₀ := lt_min (by norm_num) (by positivity)
  have hε₀1 : ε₀ ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
  have hε₀lt : ε₀ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hε₀δ : 2600 * ε₀ ≤ δ := by
    have h1 : ε₀ ≤ δ / 5200 := min_le_right _ _
    linarith [hδpos]
  have hcover : tau ⁻¹' Drho ρ ⊆ ⋃ m : ℤ × ℤ, (tau ⁻¹' Drho ρ ∩ Qsq m) := by
    intro x hx
    obtain ⟨m, hm⟩ := mem_Qsq x
    exact Set.mem_iUnion.mpr ⟨m, hx, hm⟩
  refine le_antisymm ?_ zero_le
  calc dimH (tau ⁻¹' Drho ρ)
      ≤ dimH (⋃ m : ℤ × ℤ, (tau ⁻¹' Drho ρ ∩ Qsq m)) := dimH_mono hcover
    _ = ⨆ m : ℤ × ℤ, dimH (tau ⁻¹' Drho ρ ∩ Qsq m) := dimH_iUnion _
    _ = 0 := iSup_eq_bot.mpr (fun m =>
        key_sq ρ ε₀ δ hρ hδpos hε₀pos hε₀1 hε₀lt tauiff hε₀δ hno hinj
          (hsep ε₀ hε₀pos hε₀1 hε₀δ) (hcrit ε₀ hε₀pos)
          (hsub ε₀ hε₀pos) (hcount ε₀ hε₀pos) m)

/-- **C1b**: box__thick_lattice_short_basis dimension via separated sets (EKL Lemma 8.2, Prop. 8.3). -/
theorem prove_BoxDim : Work.EKLContract.P_BoxDim := by
  intro ρ hρ hno
  obtain ⟨C, hC, hb⟩ := Work.EKLComp.thick_lattice_short_basis ρ hρ
  obtain ⟨δ, hδpos, hinj⟩ := Work.EKLComp.thick_inj_given_short ρ hρ C hC hb
  exact Work.EKLComp.boxdim_core ρ hρ hno δ hδpos
    (Work.EKLComp.tau_algebra.2.2)
    hinj
    (fun ε₀ h1 h2 h3 => Work.EKLComp.sep_at_critical_time ρ δ ε₀ hρ hδpos h1 h2 h3 hinj)
    (fun ε₀ h1 d hd hdε N hN hs => Work.EKLComp.critical_time ε₀ d h1 hd hdε N hN hs)
    (fun ε₀ h1 F hF => Work.EKLComp.subsquare_extract ε₀ h1 F hF)
    (fun ε₀ h1 S hS => Work.EKLComp.dimH_zero_of_separated (ε := ε₀ * Real.exp 3) (by positivity) hS)

end Work.EKLComp

