import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.subgroup_rayDegAux
import Submission.Work.BW.exists_det_submatrix_ne_zero
import Submission.Work.BW.boxClassCount_le_image
import Submission.Work.BW.boxImage_card_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-!
# Polynomial upper bound for the number of classes of the ray box

Given a primitive system `M : Fin ρ → Fin N → ℤ` (rows `ℚ`-linearly independent and spanning a
saturated sublattice of `ℤ^N`) and `D : Fin (N+1) →₀ ℕ`, the number of classes of the box
`∏ᵢ [0, t·D_{i+1}]` modulo the row lattice grows at most like `t^{N-ρ}`.

The proof builds an explicit `ℤ`-linear reduction map `boxMap M J hJ : ℤ^N → ℤ^{N-ρ}` with
kernel exactly the row lattice, using the adjugate of a non-singular `ρ × ρ` minor of `M` on a
column set `J`; the map sends `b` to the `Jᶜ`-coordinates of `δ·b - u·M`, where `δ = det (M|_J)`
and `u = adj(M|_J)ᵀ · b|_J`. Its coordinates on the box are bounded linearly in `t`, whence the
`t^{N-ρ}` growth.
-/

section Defs

/-- The complement of `J` has `N - ρ` elements. -/
theorem card_compl_eq {N ρ : ℕ} (J : Finset (Fin N)) (hJ : J.card = ρ) : Jᶜ.card = N - ρ := by
  rw [Finset.card_compl, Fintype.card_fin, hJ]

/-- The increasing enumeration of the complement of `J`. -/
noncomputable abbrev compEmb {N ρ : ℕ} (J : Finset (Fin N)) (hJ : J.card = ρ) :
    Fin (N - ρ) ↪o Fin N :=
  (Jᶜ).orderEmbOfFin (card_compl_eq J hJ)

/-- Membership in `Jᶜ` of the complement embedding. -/
lemma compEmb_mem {N ρ : ℕ} (J : Finset (Fin N)) (hJ : J.card = ρ) (c : Fin (N - ρ)) :
    compEmb J hJ c ∈ Jᶜ :=
  Finset.orderEmbOfFin_mem _ _ c

/-- Every element of `Jᶜ` is a value of the complement embedding. -/
lemma exists_compEmb_eq {N ρ : ℕ} (J : Finset (Fin N)) (hJ : J.card = ρ) {i : Fin N}
    (hi : i ∈ Jᶜ) : ∃ c : Fin (N - ρ), compEmb J hJ c = i := by
  have h : i ∈ Finset.image (compEmb J hJ) Finset.univ := by
    rw [Finset.image_orderEmbOfFin_univ (Jᶜ) (card_compl_eq J hJ)]
    exact hi
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp h
  exact ⟨a, ha⟩

/-- Every element of `J` is a value of the enumeration of `J`. -/
lemma exists_orderEmb_eq {N ρ : ℕ} (J : Finset (Fin N)) (hJ : J.card = ρ) {i : Fin N}
    (hi : i ∈ J) : ∃ a : Fin ρ, J.orderEmbOfFin hJ a = i := by
  have h : i ∈ Finset.image (J.orderEmbOfFin hJ) Finset.univ := by
    rw [Finset.image_orderEmbOfFin_univ J hJ]
    exact hi
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp h
  exact ⟨a, ha⟩

/-- The `ρ × ρ` matrix of the rows of `M` on the columns `J` (in increasing order). -/
abbrev colMat {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (J : Finset (Fin N)) (hJ : J.card = ρ) :
    Matrix (Fin ρ) (Fin ρ) ℤ := fun a b => M a (J.orderEmbOfFin hJ b)

/-- The adjugate of `colMat`. -/
abbrev adjMat {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (J : Finset (Fin N)) (hJ : J.card = ρ) :
    Matrix (Fin ρ) (Fin ρ) ℤ := (colMat M J hJ).adjugate

/-- The reduction map `Ψ : ℤ^N → ℤ^{N-ρ}` attached to the minor of `M` on the columns `J`:
`Ψ b` is the `Jᶜ`-part of `δ·b - u·M`, with `δ = det (M|_J)` and `u = adj(M|_J)ᵀ · b|_J`. -/
noncomputable def boxMap {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (J : Finset (Fin N)) (hJ : J.card = ρ) :
    (Fin N → ℤ) →ₗ[ℤ] (Fin (N - ρ) → ℤ) :=
  let eJ : Fin ρ ↪o Fin N := J.orderEmbOfFin hJ
  let eC : Fin (N - ρ) ↪o Fin N := compEmb J hJ
  let A : Matrix (Fin ρ) (Fin ρ) ℤ := fun a b => M a (eJ b)
  let adj : Matrix (Fin ρ) (Fin ρ) ℤ := A.adjugate
  LinearMap.pi (fun c : Fin (N - ρ) =>
    (A.det) • LinearMap.proj (R := ℤ) (φ := fun _ : Fin N => ℤ) (eC c) -
      ∑ a : Fin ρ, (M a (eC c)) •
        (∑ a' : Fin ρ, (adj a' a) • LinearMap.proj (R := ℤ) (φ := fun _ : Fin N => ℤ) (eJ a')))

/-- Evaluation formula for `boxMap`. -/
lemma boxMap_apply {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (J : Finset (Fin N)) (hJ : J.card = ρ)
    (b : Fin N → ℤ) (c : Fin (N - ρ)) :
    boxMap M J hJ b c = (minorJ M J hJ) * b (compEmb J hJ c) -
      ∑ a : Fin ρ, M a (compEmb J hJ c) *
        (∑ a' : Fin ρ, (adjMat M J hJ) a' a * b (J.orderEmbOfFin hJ a')) := by
  simp only [boxMap, compEmb, minorJ, adjMat, LinearMap.pi_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.proj_apply, smul_eq_mul]

/-- The `J`-coordinates of `δ·b` are recovered from the row combination `u·M`. -/
lemma boxMap_Jcoord {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (J : Finset (Fin N)) (hJ : J.card = ρ)
    (b : Fin N → ℤ) (a' : Fin ρ) :
    ∑ a : Fin ρ, M a (J.orderEmbOfFin hJ a') *
      (∑ i : Fin ρ, (adjMat M J hJ) i a * b (J.orderEmbOfFin hJ i)) =
    (minorJ M J hJ) * b (J.orderEmbOfFin hJ a') := by
  have hkey : ∀ i : Fin ρ,
      (adjMat M J hJ * colMat M J hJ) i a' = (minorJ M J hJ) * (if i = a' then 1 else 0) := by
    intro i
    rw [Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    rfl
  have hmul_apply : ∀ i : Fin ρ,
      (∑ a : Fin ρ, (adjMat M J hJ) i a * M a (J.orderEmbOfFin hJ a'))
        = (minorJ M J hJ) * (if i = a' then 1 else 0) := by
    intro i
    rw [← hkey i, Matrix.mul_apply]
  calc ∑ a : Fin ρ, M a (J.orderEmbOfFin hJ a') *
        (∑ i : Fin ρ, (adjMat M J hJ) i a * b (J.orderEmbOfFin hJ i))
      = ∑ i : Fin ρ, (∑ a : Fin ρ, (adjMat M J hJ) i a * M a (J.orderEmbOfFin hJ a')) *
          b (J.orderEmbOfFin hJ i) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun a _ => ?_)
        ring
    _ = (minorJ M J hJ) * b (J.orderEmbOfFin hJ a') := by
        simp only [hmul_apply]
        rw [Finset.sum_eq_single a']
        · simp
        · intro i _ hi; simp [hi]
        · intro h; exact absurd (Finset.mem_univ a') h

/-- The rows of `M` lie in the kernel of `boxMap`. -/
lemma boxMap_row_mem {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (J : Finset (Fin N)) (hJ : J.card = ρ)
    (j : Fin ρ) : boxMap M J hJ (M j) = 0 := by
  funext c
  simp only [Pi.zero_apply]
  rw [boxMap_apply]
  have hkey : ∀ a : Fin ρ,
      (∑ a' : Fin ρ, (adjMat M J hJ) a' a * M j (J.orderEmbOfFin hJ a'))
        = (minorJ M J hJ) * (if j = a then 1 else 0) := by
    intro a
    have h2 := congr_fun (congr_fun (Matrix.mul_adjugate (colMat M J hJ)) j) a
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, colMat] at h2
    rw [Finset.sum_congr rfl (fun a' (_ : a' ∈ Finset.univ) => mul_comm _ _)]
    exact h2
  have hpt : ∀ a : Fin ρ, M a (compEmb J hJ c) * ((minorJ M J hJ) * (if j = a then 1 else 0))
      = if j = a then (minorJ M J hJ) * M a (compEmb J hJ c) else 0 := by
    intro a
    by_cases h : j = a <;> simp [h, mul_comm]
  have hsum : (∑ a : Fin ρ, M a (compEmb J hJ c) * ((minorJ M J hJ) * (if j = a then 1 else 0)))
      = (minorJ M J hJ) * M j (compEmb J hJ c) := by
    rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hpt a)]
    rw [Finset.sum_ite_eq Finset.univ j]
    simp
  simp only [hkey, hsum]
  ring

/-- The kernel of `boxMap` is exactly the row lattice, for a primitive system (the saturation
hypothesis is used here). -/
theorem boxMap_ker {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (hM : PrimSys M) (J : Finset (Fin N))
    (hJ : J.card = ρ) (hΔ : minorJ M J hJ ≠ 0) :
    LinearMap.ker (boxMap M J hJ) = rowLat N ρ M := by
  refine le_antisymm ?_ ?_
  · intro b hb
    rw [LinearMap.mem_ker] at hb
    have hvec : (minorJ M J hJ) • b =
        ∑ a : Fin ρ,
          (∑ a' : Fin ρ, (adjMat M J hJ) a' a * b (J.orderEmbOfFin hJ a')) • (M a) := by
      funext i
      rcases Finset.mem_union.mp (show i ∈ J ∪ Jᶜ by simp) with hi | hi
      · obtain ⟨a', -, rfl⟩ := exists_orderEmb_eq J hJ hi
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        simpa [mul_comm, mul_left_comm, mul_assoc] using (boxMap_Jcoord M J hJ b a').symm
      · obtain ⟨c, rfl⟩ := exists_compEmb_eq J hJ hi
        have hc := congr_fun hb c
        rw [boxMap_apply] at hc
        have hc' : (minorJ M J hJ) * b (compEmb J hJ c) =
            ∑ a : Fin ρ, M a (compEmb J hJ c) *
              (∑ a' : Fin ρ, (adjMat M J hJ) a' a * b (J.orderEmbOfFin hJ a')) :=
          sub_eq_zero.mp hc
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [hc']
        exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
    have hmem : (minorJ M J hJ) • b ∈ rowLat N ρ M := by
      rw [hvec]
      exact Submodule.sum_mem _ (fun a _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
    exact hM.2 b (minorJ M J hJ) hΔ hmem
  · rw [rowLat, Submodule.span_le]
    rintro x ⟨j, rfl⟩
    exact LinearMap.mem_ker.mpr (boxMap_row_mem M J hJ j)

/-- The constant of the coordinate bound for `boxMap`. -/
noncomputable abbrev boxMapK {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (J : Finset (Fin N))
    (hJ : J.card = ρ) (c : Fin (N - ρ)) : ℤ :=
  |minorJ M J hJ| + ∑ a : Fin ρ, (∑ a' : Fin ρ, |adjMat M J hJ a' a|) * |M a (compEmb J hJ c)|

lemma boxMapK_nonneg {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (J : Finset (Fin N)) (hJ : J.card = ρ)
    (c : Fin (N - ρ)) : 0 ≤ boxMapK M J hJ c := by
  rw [boxMapK]
  exact add_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun a _ =>
    mul_nonneg (Finset.sum_nonneg (fun a' _ => abs_nonneg _)) (abs_nonneg _)))

/-- Coordinates of box points under the box map. -/
lemma boxPts_bounds {N : ℕ} {m : Fin N → ℕ} {b : Fin N → ℤ} (hb : b ∈ boxPts N m) :
    ∀ i, 0 ≤ b i ∧ b i ≤ (m i : ℤ) := by
  rw [boxPts] at hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
  intro i
  have h1 := (Finset.mem_pi.mp hx) i (Finset.mem_univ i)
  have h2 : x i (Finset.mem_univ i) ≤ m i := Nat.lt_succ_iff.mp (Finset.mem_range.mp h1)
  exact ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr h2⟩

/-- Coordinate bound: on the box `∏ᵢ [0, mᵢ]` the coordinates of `boxMap` are bounded by
`boxMapK · sup m`. -/
lemma boxMap_coord_bound {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (J : Finset (Fin N)) (hJ : J.card = ρ)
    {m : Fin N → ℕ} {b : Fin N → ℤ} (hb : b ∈ boxPts N m) (c : Fin (N - ρ)) :
    |boxMap M J hJ b c| ≤ boxMapK M J hJ c * ((Finset.univ.sup m : ℕ) : ℤ) := by
  set S : ℤ := ((Finset.univ.sup m : ℕ) : ℤ) with hSdef
  have hS : 0 ≤ S := Int.natCast_nonneg _
  have hbnd := boxPts_bounds hb
  have hle : ∀ i : Fin N, b i ≤ S := by
    intro i
    have h1 : (m i : ℤ) ≤ S := by
      rw [hSdef]; exact_mod_cast Finset.le_sup (f := m) (Finset.mem_univ i)
    exact le_trans (hbnd i).2 h1
  have habs : ∀ i : Fin N, |b i| ≤ S := by
    intro i
    rw [abs_le]
    exact ⟨by linarith [(hbnd i).1, hS], hle i⟩
  have hinner : ∀ a : Fin ρ,
      |∑ a' : Fin ρ, (adjMat M J hJ) a' a * b (J.orderEmbOfFin hJ a')|
        ≤ (∑ a' : Fin ρ, |(adjMat M J hJ) a' a|) * S := by
    intro a
    calc |∑ a' : Fin ρ, (adjMat M J hJ) a' a * b (J.orderEmbOfFin hJ a')|
        ≤ ∑ a' : Fin ρ, |(adjMat M J hJ) a' a * b (J.orderEmbOfFin hJ a')| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a' : Fin ρ, |(adjMat M J hJ) a' a| * |b (J.orderEmbOfFin hJ a')| := by
          simp [abs_mul]
      _ ≤ ∑ a' : Fin ρ, |(adjMat M J hJ) a' a| * S :=
          Finset.sum_le_sum (fun a' _ => mul_le_mul_of_nonneg_left (habs _) (abs_nonneg _))
      _ = (∑ a' : Fin ρ, |(adjMat M J hJ) a' a|) * S := (Finset.sum_mul _ _ _).symm
  have step1 : |(minorJ M J hJ) * b (compEmb J hJ c) -
      ∑ a, M a (compEmb J hJ c) *
        (∑ a', (adjMat M J hJ) a' a * b (J.orderEmbOfFin hJ a'))|
      ≤ |(minorJ M J hJ) * b (compEmb J hJ c)| +
        |∑ a, M a (compEmb J hJ c) *
          (∑ a', (adjMat M J hJ) a' a * b (J.orderEmbOfFin hJ a'))| := by
    have h := abs_add_le ((minorJ M J hJ) * b (compEmb J hJ c))
      (-(∑ a, M a (compEmb J hJ c) *
        (∑ a', (adjMat M J hJ) a' a * b (J.orderEmbOfFin hJ a'))))
    rw [abs_neg] at h
    simpa [sub_eq_add_neg] using h
  have key : |boxMap M J hJ b c| ≤ |minorJ M J hJ| * S +
      ∑ a : Fin ρ, |M a (compEmb J hJ c)| *
        ((∑ a' : Fin ρ, |(adjMat M J hJ) a' a|) * S) := by
    rw [boxMap_apply]
    refine le_trans step1 (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (habs _) (abs_nonneg _)
    · refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum (fun a _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hinner a) (abs_nonneg _)
  refine le_trans key ?_
  rw [boxMapK]
  have hsum : (∑ a : Fin ρ, |M a (compEmb J hJ c)| *
        ((∑ a' : Fin ρ, |(adjMat M J hJ) a' a|) * S))
      = (∑ a : Fin ρ, (∑ a' : Fin ρ, |(adjMat M J hJ) a' a|) *
          |M a (compEmb J hJ c)|) * S := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  rw [hsum]
  apply le_of_eq
  ring_nf

/-- A non-singular maximal minor exists for a matrix with linearly independent rows. -/
lemma minorJ_exists_ne_zero {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ)
    (hlin : LinearIndependent ℚ (fun j i => (M j i : ℚ))) :
    ∃ (J : Finset (Fin N)) (hJ : J.card = ρ), minorJ M J hJ ≠ 0 := by
  obtain ⟨J, hJ, hdet⟩ :=
    exists_det_submatrix_ne_zero (K := ℚ) (A := fun j i => (M j i : ℚ)) hlin
  refine ⟨J, hJ, fun h0 => hdet ?_⟩
  have hcast : ((minorJ M J hJ : ℤ) : ℚ)
      = (Matrix.submatrix (fun j i => (M j i : ℚ)) id (J.orderEmbOfFin hJ)).det := by
    have h1 : (Matrix.map (colMat M J hJ) (Int.castRingHom ℚ)).det
        = (Matrix.submatrix (fun j i => (M j i : ℚ)) id (J.orderEmbOfFin hJ)).det := by
      congr 1
    rw [← h1]
    exact Int.cast_det (colMat M J hJ)
  rw [h0, Int.cast_zero] at hcast
  exact hcast.symm

end Defs

/-- Polynomial upper bound for the number of classes of the ray box: for a primitive system `M : Fin ρ → Fin N → ℤ` and `D : Fin (N+1) →₀ ℕ` there is `C : ℚ` with `#(box ∏ᵢ[0, t·D_{i+1}] mod rowLat M) ≤ C · t^{N-ρ}` for all `t ≥ 1`. (Use `Φ : ℤ^N → ℤ^{N-ρ}` with kernel the row lattice; the classes are the values `Φ b`, so the count is at most `∏_k (1 + ∑ᵢ t·D_{i+1}·|Φ(eᵢ)_k|)`; you may import `Submission.Work.BW.rowLat_quotient` if it is available, otherwise prove the existence of `Φ` inline.) -/
theorem boxClass_upper {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (hM : PrimSys M) (D : Fin (N + 1) →₀ ℕ) :
    ∃ C : ℚ, ∀ t : ℕ, 1 ≤ t →
      (boxClassCount N ρ M (fun i => t * D i.succ) : ℚ) ≤ C * (t : ℚ) ^ (N - ρ) := by
  obtain ⟨J, hJ, hΔ⟩ := minorJ_exists_ne_zero M hM.1
  set Dm : ℕ := Finset.univ.sup (fun i : Fin N => D i.succ) with hDm
  refine ⟨∏ c : Fin (N - ρ), (((2 * ((boxMapK M J hJ c).toNat * Dm) + 1 : ℕ)) : ℚ), ?_⟩
  intro t ht
  set m : Fin N → ℕ := fun i => t * D i.succ with hm
  have hker := boxMap_ker M hM J hJ hΔ
  have hcoord : ∀ b ∈ boxPts N m, ∀ c : Fin (N - ρ),
      |(boxMap M J hJ b) c| ≤ ((((boxMapK M J hJ c).toNat : ℕ)) : ℤ) *
        ((Finset.univ.sup m : ℕ) : ℤ) := by
    intro b hb c
    have hK : ((((boxMapK M J hJ c).toNat : ℕ)) : ℤ) = boxMapK M J hJ c :=
      Int.toNat_of_nonneg (boxMapK_nonneg M J hJ c)
    rw [hK]
    exact boxMap_coord_bound M J hJ hb c
  have h1 := boxClassCount_le_image M (boxMap M J hJ) hker m
  have h2 := boxImage_card_le m (boxMap M J hJ) (fun c => (boxMapK M J hJ c).toNat) hcoord
  have hsup : Finset.univ.sup m ≤ t * Dm := by
    rw [Finset.sup_le_iff]
    intro i _
    show t * D i.succ ≤ t * Dm
    exact Nat.mul_le_mul_left t (by
      rw [hDm]
      exact Finset.le_sup (f := fun i : Fin N => D i.succ) (Finset.mem_univ i))
  have h3 : ∀ c : Fin (N - ρ),
      2 * ((boxMapK M J hJ c).toNat * Finset.univ.sup m) + 1
        ≤ (2 * ((boxMapK M J hJ c).toNat * Dm) + 1) * t := by
    intro c
    have hA : 2 * ((boxMapK M J hJ c).toNat * Finset.univ.sup m)
        ≤ 2 * ((boxMapK M J hJ c).toNat * Dm) * t := by
      calc 2 * ((boxMapK M J hJ c).toNat * Finset.univ.sup m)
          ≤ 2 * ((boxMapK M J hJ c).toNat * (t * Dm)) :=
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hsup)
        _ = 2 * ((boxMapK M J hJ c).toNat * Dm) * t := by ring
    calc 2 * ((boxMapK M J hJ c).toNat * Finset.univ.sup m) + 1
        ≤ 2 * ((boxMapK M J hJ c).toNat * Dm) * t + t := Nat.add_le_add hA ht
      _ = (2 * ((boxMapK M J hJ c).toNat * Dm) + 1) * t := by ring
  have h4 : (∏ c : Fin (N - ρ), (2 * ((boxMapK M J hJ c).toNat * Finset.univ.sup m) + 1))
      ≤ ∏ c : Fin (N - ρ), ((2 * ((boxMapK M J hJ c).toNat * Dm) + 1) * t) :=
    Finset.prod_le_prod (fun c _ => h3 c)
  have h5 : (∏ c : Fin (N - ρ), ((2 * ((boxMapK M J hJ c).toNat * Dm) + 1) * t))
      = (∏ c : Fin (N - ρ), (2 * ((boxMapK M J hJ c).toNat * Dm) + 1)) * t ^ (N - ρ) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h6 : (((∏ c : Fin (N - ρ),
        ((2 * ((boxMapK M J hJ c).toNat * Dm) + 1) * t)) : ℕ) : ℚ)
      = (∏ c : Fin (N - ρ), ((2 * ((boxMapK M J hJ c).toNat * Dm) + 1 : ℕ) : ℚ)) *
        (t : ℚ) ^ (N - ρ) := by
    rw [h5]
    push_cast
    ring
  calc (boxClassCount N ρ M m : ℚ)
      ≤ (((boxPts N m).image (boxMap M J hJ)).card : ℚ) := by exact_mod_cast h1
    _ ≤ (((∏ c : Fin (N - ρ),
          (2 * ((boxMapK M J hJ c).toNat * Finset.univ.sup m) + 1)) : ℕ) : ℚ) := by
        exact_mod_cast h2
    _ ≤ (((∏ c : Fin (N - ρ),
          ((2 * ((boxMapK M J hJ c).toNat * Dm) + 1) * t)) : ℕ) : ℚ) := by exact_mod_cast h4
    _ = (∏ c : Fin (N - ρ), ((2 * ((boxMapK M J hJ c).toNat * Dm) + 1 : ℕ) : ℚ)) *
          (t : ℚ) ^ (N - ρ) := h6

end Work.BW
