import Mathlib

/-!
# Counting the points of a separated set that come close to the integer lattice

This file proves `Work.Pert.card_band_lattice_le`: for a finset `B` of indices and a
real "walk" `t : ℕ → ℝ` whose values

* all lie within a window of width `P` (`hspan`), and
* satisfy the separation `t j + γ (j' - j) ≤ t j'` for `j < j'` in `B` (`hsep`),

the number of `j ∈ B` whose value `t j` is within `s` of an integer is at most
`(P + 2 s + 2) (2 s / γ + 2)`.

The proof attaches to each good index the nearest integer (via the explicit
`bandLatticeNear`), groups the good indices by this integer, and bounds

* the number of indices attached to a single integer (they lie within `[k - s, k + s]`,
  an interval of length `2 s`, and are `γ`-separated), and
* the number of integers that can occur (they lie in `[t j₀ - s, t j₀ + P + s]`).
-/

namespace Work.Pert

/-- The integer nearest to `x`, chosen between `⌊x⌋` and `⌊x⌋ + 1`. -/
noncomputable def bandLatticeNear (x : ℝ) : ℤ :=
  if dist x (⌊x⌋ : ℝ) ≤ dist x ((⌊x⌋ + 1 : ℤ) : ℝ) then ⌊x⌋ else ⌊x⌋ + 1

/-- `bandLatticeNear x` realises the minimum of the distances from `x` to the
two integers surrounding it. -/
lemma dist_bandLatticeNear (x : ℝ) :
    dist x ((bandLatticeNear x : ℤ) : ℝ) =
      min (dist x ((⌊x⌋ : ℤ) : ℝ)) (dist x (((⌊x⌋ + 1 : ℤ)) : ℝ)) := by
  unfold bandLatticeNear
  split_ifs with hc
  · exact (min_eq_left hc).symm
  · exact (min_eq_right (le_of_not_ge hc)).symm

/-- The minimum of the distances from `x` to the two integers surrounding it is a
lower bound for the distance from `x` to any integer; hence it is below the
infimum over all integers. -/
lemma min_le_iInf_dist_bandLattice (x : ℝ) :
    min (dist x ((⌊x⌋ : ℤ) : ℝ)) (dist x (((⌊x⌋ + 1 : ℤ)) : ℝ))
      ≤ (⨅ k : ℤ, dist x (k : ℝ)) := by
  apply le_ciInf
  intro k
  by_cases hk : k ≤ ⌊x⌋
  · have hkx : ((k : ℤ) : ℝ) ≤ ((⌊x⌋ : ℤ) : ℝ) := by exact_mod_cast hk
    have hnx : ((⌊x⌋ : ℤ) : ℝ) ≤ x := Int.floor_le x
    have hdist_k : dist x ((k : ℤ) : ℝ) = x - ((k : ℤ) : ℝ) := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    have hdist_n : dist x ((⌊x⌋ : ℤ) : ℝ) = x - ((⌊x⌋ : ℤ) : ℝ) := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    calc min (dist x ((⌊x⌋ : ℤ) : ℝ)) (dist x (((⌊x⌋ + 1 : ℤ)) : ℝ))
          ≤ dist x ((⌊x⌋ : ℤ) : ℝ) := min_le_left _ _
      _ = x - ((⌊x⌋ : ℤ) : ℝ) := hdist_n
      _ ≤ x - ((k : ℤ) : ℝ) := by linarith [hkx]
      _ = dist x ((k : ℤ) : ℝ) := hdist_k.symm
  · have hcast1 : (((⌊x⌋ + 1 : ℤ)) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) + 1 := by push_cast; ring
    have hkx : (((⌊x⌋ + 1 : ℤ)) : ℝ) ≤ ((k : ℤ) : ℝ) := by
      have h1 : ⌊x⌋ + 1 ≤ k := by omega
      exact_mod_cast h1
    have hx_lt : x < ((⌊x⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one x
    have hdist_k : dist x ((k : ℤ) : ℝ) = ((k : ℤ) : ℝ) - x := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith)]; ring
    have hdist_n : dist x (((⌊x⌋ + 1 : ℤ)) : ℝ) = (((⌊x⌋ + 1 : ℤ)) : ℝ) - x := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith)]; ring
    calc min (dist x ((⌊x⌋ : ℤ) : ℝ)) (dist x (((⌊x⌋ + 1 : ℤ)) : ℝ))
          ≤ dist x (((⌊x⌋ + 1 : ℤ)) : ℝ) := min_le_right _ _
      _ = (((⌊x⌋ + 1 : ℤ)) : ℝ) - x := hdist_n
      _ ≤ ((k : ℤ) : ℝ) - x := by linarith [hkx]
      _ = dist x ((k : ℤ) : ℝ) := hdist_k.symm

/-- If `x` is within distance `s` of the lattice `ℤ`, then the explicit nearest
integer `bandLatticeNear x` already witnesses this. -/
lemma bandLatticeNear_spec (x s : ℝ)
    (h : (⨅ k : ℤ, dist x (k : ℝ)) ≤ s) :
    dist x ((bandLatticeNear x : ℤ) : ℝ) ≤ s := by
  rw [dist_bandLatticeNear]
  exact le_trans (min_le_iInf_dist_bandLattice x) h

/-- Counting the points of a separated set that come close to the integer lattice. -/
theorem card_band_lattice_le {B : Finset ℕ} {t : ℕ → ℝ} {γ P s : ℝ}
    (hγ : 0 < γ) (hP : 0 ≤ P) (hs : 0 ≤ s)
    (hspan : ∀ j ∈ B, ∀ j' ∈ B, |t j - t j'| ≤ P)
    (hsep : ∀ j ∈ B, ∀ j' ∈ B, j < j' → t j + γ * ((j' - j : ℕ) : ℝ) ≤ t j') :
    (((B.filter (fun j => (⨅ k : ℤ, dist (t j) (k : ℝ)) ≤ s)).card : ℝ))
        ≤ (P + 2 * s + 2) * (2 * s / γ + 2) := by
  classical
  set A : Finset ℕ := B.filter (fun j => (⨅ k : ℤ, dist (t j) (k : ℝ)) ≤ s) with hAdef
  have hAmem : ∀ j, j ∈ A ↔ j ∈ B ∧ (⨅ k : ℤ, dist (t j) (k : ℝ)) ≤ s := by
    intro j; rw [hAdef, Finset.mem_filter]
  have hUniv : (0:ℝ) ≤ P + 2*s + 2 := by linarith
  have hden : (0:ℝ) ≤ 2*s/γ + 1 := by
    have h1 : (0:ℝ) ≤ 2*s := by linarith
    have h2 : (0:ℝ) ≤ 2*s/γ := div_nonneg h1 hγ.le
    linarith
  -- On `B` the walk `t` is strictly increasing, and hence wide-sense increasing.
  have hmonoB : ∀ j ∈ B, ∀ j' ∈ B, j < j' → t j < t j' := by
    intro j hj j' hj' hlt
    have hstep := hsep j hj j' hj' hlt
    have hpos : (0:ℝ) < ((j' - j : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hlt
    have : 0 < γ * ((j' - j : ℕ) : ℝ) := mul_pos hγ hpos
    linarith
  have hmonoB_le : ∀ j ∈ B, ∀ j' ∈ B, j ≤ j' → t j ≤ t j' := by
    intro j hj j' hj' hle
    rcases lt_or_eq_of_le hle with h | h
    · exact le_of_lt (hmonoB j hj j' hj' h)
    · rw [h]
  rcases A.eq_empty_or_nonempty with hA0 | hAne
  · rw [hA0]; simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hUniv (by linarith : (0:ℝ) ≤ 2*s/γ + 2)
  · have hmain : (A.card : ℝ) ≤ (P + 2*s + 2) * (2*s/γ + 1) := by
      -- A reference point of `B`, the minimum index of `A`.
      set j0 : ℕ := A.min' hAne with hj0
      have hj0_mem : j0 ∈ A := by rw [hj0]; exact Finset.min'_mem A hAne
      have hj0B : j0 ∈ B := ((hAmem j0).mp hj0_mem).1
      have hj0_le : ∀ j ∈ A, j0 ≤ j := by
        intro j hj; rw [hj0]; exact Finset.min'_le A j hj
      have hnn_spec : ∀ j ∈ A, dist (t j) ((bandLatticeNear (t j) : ℤ) : ℝ) ≤ s := by
        intro j hj; exact bandLatticeNear_spec (t j) s ((hAmem j).mp hj).2
      -- ## Fibre bound: at most `2 s / γ + 1` good indices per integer.
      have hfiber : ∀ k : ℤ,
          ((A.filter (fun j => bandLatticeNear (t j) = k)).card : ℝ) ≤ 2*s/γ + 1 := by
        intro k
        set S : Finset ℕ := A.filter (fun j => bandLatticeNear (t j) = k) with hS
        have hmemS : ∀ j, j ∈ S ↔ j ∈ A ∧ bandLatticeNear (t j) = k := by
          intro j; rw [hS, Finset.mem_filter]
        rcases S.eq_empty_or_nonempty with hS0 | hSne
        · rw [hS0]; simp only [Finset.card_empty, Nat.cast_zero]; exact hden
        · have hjminS : S.min' hSne ∈ S := Finset.min'_mem S hSne
          have hjmaxS : S.max' hSne ∈ S := Finset.max'_mem S hSne
          have hminA : S.min' hSne ∈ A := ((hmemS _).mp hjminS).1
          have hmaxA : S.max' hSne ∈ A := ((hmemS _).mp hjmaxS).1
          have hminB : S.min' hSne ∈ B := ((hAmem _).mp hminA).1
          have hmaxB : S.max' hSne ∈ B := ((hAmem _).mp hmaxA).1
          have hmin_nn : bandLatticeNear (t (S.min' hSne)) = k := ((hmemS _).mp hjminS).2
          have hmax_nn : bandLatticeNear (t (S.max' hSne)) = k := ((hmemS _).mp hjmaxS).2
          have hdist_min : dist (t (S.min' hSne)) (k:ℝ) ≤ s := by
            have h := hnn_spec _ hminA; rwa [hmin_nn] at h
          have hdist_max : dist (t (S.max' hSne)) (k:ℝ) ≤ s := by
            have h := hnn_spec _ hmaxA; rwa [hmax_nn] at h
          have hle : S.min' hSne ≤ S.max' hSne := Finset.min'_le S _ hjmaxS
          have hspan2s : t (S.max' hSne) - t (S.min' hSne) ≤ 2*s := by
            rw [Real.dist_eq, abs_le] at hdist_min hdist_max
            linarith [hdist_min.1, hdist_min.2, hdist_max.1, hdist_max.2]
          have hγX : γ * ((S.max' hSne - S.min' hSne : ℕ) : ℝ) ≤ 2*s := by
            rcases lt_or_eq_of_le hle with hlt | heq
            · have hh := hsep _ hminB _ hmaxB hlt
              linarith
            · rw [← heq]; simp only [Nat.sub_self, Nat.cast_zero, mul_zero]; linarith [hs]
          have hratio : ((S.max' hSne - S.min' hSne : ℕ) : ℝ) ≤ 2*s/γ := by
            rw [le_div_iff₀ hγ, mul_comm]; exact hγX
          have hsub : S ⊆ Finset.Icc (S.min' hSne) (S.max' hSne) := fun j hj =>
            Finset.mem_Icc.mpr ⟨Finset.min'_le S j hj, Finset.le_max' S j hj⟩
          have h1 : S.card ≤ S.max' hSne - S.min' hSne + 1 := by
            calc S.card ≤ (Finset.Icc (S.min' hSne) (S.max' hSne)).card :=
                  Finset.card_le_card hsub
              _ = S.max' hSne + 1 - S.min' hSne := Nat.card_Icc _ _
              _ = S.max' hSne - S.min' hSne + 1 := by omega
          have h2 : (S.card : ℝ) ≤ ((S.max' hSne - S.min' hSne + 1 : ℕ) : ℝ) := by
            exact_mod_cast h1
          have h3 : ((S.max' hSne - S.min' hSne + 1 : ℕ) : ℝ)
              = ((S.max' hSne - S.min' hSne : ℕ) : ℝ) + 1 := by
            rw [Nat.cast_add, Nat.cast_one]
          rw [h3] at h2
          linarith [hratio]
      -- ## Image bound: the nearest integers range over a window of width `P + 2 s + 1`.
      have himg_sub : A.image (fun j => bandLatticeNear (t j))
          ⊆ Finset.Icc ⌈t j0 - s⌉ ⌊t j0 + P + s⌋ := by
        intro k hk
        obtain ⟨j, hjA, rfl⟩ := Finset.mem_image.mp hk
        have hdist := hnn_spec j hjA
        rw [Real.dist_eq, abs_le] at hdist
        have hjB : j ∈ B := ((hAmem j).mp hjA).1
        have htj0le : t j0 ≤ t j := hmonoB_le j0 hj0B j hjB (hj0_le j hjA)
        have htle : t j ≤ t j0 + P := by
          have hsp := hspan j hjB j0 hj0B
          rw [abs_le] at hsp
          linarith [hsp.2]
        refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
        · have hnn_ge : t j0 - s ≤ ((bandLatticeNear (t j) : ℤ) : ℝ) := by
            linarith [hdist.1, htj0le]
          exact Int.ceil_le.mpr hnn_ge
        · have hnn_le : ((bandLatticeNear (t j) : ℤ) : ℝ) ≤ t j0 + P + s := by
            linarith [hdist.2, htle]
          exact Int.le_floor.mpr hnn_le
      have hcard_img : ((A.image (fun j => bandLatticeNear (t j))).card : ℝ) ≤ P + 2*s + 2 := by
        have h1 : (A.image (fun j => bandLatticeNear (t j))).card
            ≤ (⌊t j0 + P + s⌋ + 1 - ⌈t j0 - s⌉).toNat := by
          calc (A.image (fun j => bandLatticeNear (t j))).card
              ≤ (Finset.Icc ⌈t j0 - s⌉ ⌊t j0 + P + s⌋).card :=
                Finset.card_le_card himg_sub
            _ = (⌊t j0 + P + s⌋ + 1 - ⌈t j0 - s⌉).toNat := Int.card_Icc _ _
        have h2 : ((⌊t j0 + P + s⌋ + 1 - ⌈t j0 - s⌉).toNat : ℝ) ≤ P + 2*s + 2 := by
          by_cases hnonneg : (0:ℤ) ≤ ⌊t j0 + P + s⌋ + 1 - ⌈t j0 - s⌉
          · have hz : ((⌊t j0 + P + s⌋ + 1 - ⌈t j0 - s⌉ : ℤ) : ℝ) ≤ P + 2*s + 1 := by
              have hfl : ((⌊t j0 + P + s⌋ : ℤ) : ℝ) ≤ t j0 + P + s := Int.floor_le _
              have hce : t j0 - s ≤ ((⌈t j0 - s⌉ : ℤ) : ℝ) := Int.le_ceil _
              push_cast; linarith
            calc ((⌊t j0 + P + s⌋ + 1 - ⌈t j0 - s⌉).toNat : ℝ)
                = (((⌊t j0 + P + s⌋ + 1 - ⌈t j0 - s⌉).toNat : ℤ) : ℝ) := by push_cast; ring
              _ = ((⌊t j0 + P + s⌋ + 1 - ⌈t j0 - s⌉ : ℤ) : ℝ) := by
                    rw [Int.toNat_of_nonneg hnonneg]
              _ ≤ P + 2*s + 1 := hz
              _ ≤ P + 2*s + 2 := by linarith
          · have hcast : (⌊t j0 + P + s⌋ + 1 - ⌈t j0 - s⌉).toNat = 0 :=
              Int.toNat_of_nonpos (not_le.mp hnonneg).le
            rw [hcast]; push_cast; linarith
        exact le_trans
          (by exact_mod_cast h1 : ((A.image (fun j => bandLatticeNear (t j))).card : ℝ)
              ≤ ((⌊t j0 + P + s⌋ + 1 - ⌈t j0 - s⌉).toNat : ℝ)) h2
      -- ## Assembly: split `A` by its nearest integer.
      have hfibsum := Finset.card_eq_sum_card_fiberwise (s := A)
        (f := (fun j => bandLatticeNear (t j)))
        (t := A.image (fun j => bandLatticeNear (t j)))
        (fun j hj => Finset.mem_image_of_mem _ hj)
      have hcast2 : (A.card : ℝ)
          = ∑ k ∈ A.image (fun j => bandLatticeNear (t j)),
              ((A.filter (fun j => bandLatticeNear (t j) = k)).card : ℝ) := by
        rw [hfibsum]; push_cast; rfl
      calc (A.card : ℝ)
          = ∑ k ∈ A.image (fun j => bandLatticeNear (t j)),
              ((A.filter (fun j => bandLatticeNear (t j) = k)).card : ℝ) := hcast2
        _ ≤ ∑ _k ∈ A.image (fun j => bandLatticeNear (t j)), (2*s/γ + 1) :=
            Finset.sum_le_sum (fun k _ => hfiber k)
        _ = ((A.image (fun j => bandLatticeNear (t j))).card : ℝ) * (2*s/γ + 1) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (P + 2*s + 2) * (2*s/γ + 1) := mul_le_mul_of_nonneg_right hcard_img hden
    exact le_trans hmain
      (mul_le_mul_of_nonneg_left (by linarith : (2*s/γ + 1 : ℝ) ≤ 2*s/γ + 2) hUniv)

end Work.Pert
