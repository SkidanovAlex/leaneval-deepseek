import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

open scoped BigOperators

namespace Commons.NumberTheory.DiophantineApproximation

open Matrix

lemma exists_int_abs_sub_le_half (x : ℝ) : ∃ z : ℤ, |x - (z : ℝ)| ≤ 1 / 2 := by
  refine ⟨⌊x + 1 / 2⌋, ?_⟩
  have h1 := Int.floor_le (x + 1 / 2)
  have h2 := Int.lt_floor_add_one (x + 1 / 2)
  rw [abs_le]
  constructor <;> linarith

lemma det_map_intCast_of_unitriangular {n : ℕ} (U : Matrix (Fin n) (Fin n) ℤ)
    (hd : ∀ i, U i i = 1) (ht : ∀ i j, j < i → U i j = 0) :
    (U.map (Int.castRingHom ℝ)).det = 1 := by
  have key : (U.map ⇑(Int.castRingHom ℝ)).det = ((U.det : ℤ) : ℝ) := by
    rw [show U.map ⇑(Int.castRingHom ℝ) = (Int.castRingHom ℝ).mapMatrix U from rfl]
    rw [← RingHom.map_det]
    rfl
  rw [key]
  have htri : U.IsUpperTriangular := fun i j hij => ht i j hij
  rw [Matrix.det_of_isUpperTriangular htri]
  simp [hd]

theorem submatrix_succAbove_castSucc_det_ne_zero {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.det ≠ 0)
    (p : Fin (n + 1)) (β : Fin n → ℝ)
    (hrel : ∀ b : Fin n, ∑ a : Fin n, β a * A (Fin.succAbove p a) (Fin.castSucc b)
      = A p (Fin.castSucc b)) :
    (A.submatrix (Fin.succAbove p) Fin.castSucc).det ≠ 0 := by
  intro hdet
  rw [← Matrix.exists_mulVec_eq_zero_iff] at hdet
  obtain ⟨c, hc0, hc⟩ := hdet
  have hc' : ∀ a : Fin n, ∑ b : Fin n,
      A (Fin.succAbove p a) (Fin.castSucc b) * c b = 0 := by
    intro a
    have h := congrFun hc a
    simp only [Pi.zero_apply, Matrix.mulVec_apply, dotProduct, Matrix.row,
      Matrix.submatrix_apply] at h
    exact h
  set w : Fin (n + 1) → ℝ :=
    fun k => Fin.lastCases (motive := fun _ => ℝ) 0 (fun b => c b) k with hw
  have hwcs : ∀ b : Fin n, w (Fin.castSucc b) = c b := by
    intro b; rw [hw]; simp [Fin.lastCases_castSucc]
  have hwl : w (Fin.last n) = 0 := by
    rw [hw]; simp [Fin.lastCases_last]
  have hAw : A *ᵥ w = 0 := by
    funext m
    rw [Matrix.mulVec_apply, dotProduct, Pi.zero_apply, Fin.sum_univ_castSucc]
    rw [hwl, mul_zero, add_zero]
    simp only [hwcs]
    by_cases hmp : m = p
    · rw [hmp]
      calc ∑ b : Fin n, A p (Fin.castSucc b) * c b
          = ∑ b : Fin n, (∑ a : Fin n, β a * A (Fin.succAbove p a) (Fin.castSucc b)) * c b := by
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [← hrel b]
        _ = ∑ b : Fin n, ∑ a : Fin n,
              (β a * A (Fin.succAbove p a) (Fin.castSucc b)) * c b := by
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [Finset.sum_mul]
        _ = ∑ a : Fin n, ∑ b : Fin n,
              (β a * A (Fin.succAbove p a) (Fin.castSucc b)) * c b := Finset.sum_comm
        _ = ∑ a : Fin n, β a * (∑ b : Fin n,
              A (Fin.succAbove p a) (Fin.castSucc b) * c b) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro b _
            ring
        _ = 0 := by
            refine Finset.sum_eq_zero ?_
            intro a _
            rw [hc' a, mul_zero]
    · obtain ⟨a, rfl⟩ := (Fin.eq_self_or_eq_succAbove p m).resolve_left hmp
      exact hc' a
  have hw0 : w = 0 := Matrix.eq_zero_of_mulVec_eq_zero hA hAw
  apply hc0
  funext b
  rw [← hwcs b, hw0]
  rfl

def GB (N : ℕ) (C : ℝ) : Prop :=
  ∀ (A : Matrix (Fin N) (Fin N) ℝ), A.det ≠ 0 → ∀ (lam : Fin N → ℝ),
    (∀ j, 0 < lam j) → (∀ i j, i ≤ j → lam i ≤ lam j) →
    (∀ i j, |A i j| ≤ lam j) →
    ∃ (U : Matrix (Fin N) (Fin N) ℤ) (π : Equiv.Perm (Fin N)),
      (∀ i, U i i = 1) ∧ (∀ i j, j < i → U i j = 0) ∧
      (∀ i j, |∑ k, A (π i) k * (U k j : ℝ)| ≤ C * min (lam i) (lam j))

lemma GB_zero : GB 0 1 := by
  intro A hA lam h1 h2 h3
  refine ⟨0, Equiv.refl (Fin 0), ?_, ?_, ?_⟩
  · intro i; exact i.elim0
  · intro i; exact i.elim0
  · intro i; exact i.elim0

set_option maxHeartbeats 8000000 in
lemma GB_succ {n : ℕ} {C : ℝ} (hC : 0 < C) (ih : GB n C) :
    GB (n + 1) (max C ((n : ℝ) ^ 2 * C + (n : ℝ) + 1)) := by
  intro A hA lam hpos hmono hbnd
  set K : ℝ := max C ((n : ℝ) ^ 2 * C + (n : ℝ) + 1) with hKdef
  have hK1 : C ≤ K := le_max_left _ _
  have hK2 : (n : ℝ) ^ 2 * C + (n : ℝ) + 1 ≤ K := le_max_right _ _
  have hKpos : 0 < K := lt_of_lt_of_le hC hK1
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnC : (n : ℝ) * C ≤ K := by
    have hn1 : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h]
      · have h1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
        nlinarith
    have h3 : (n : ℝ) * C ≤ (n : ℝ) ^ 2 * C := by nlinarith [mul_nonneg hn1 hC.le]
    linarith
  have hKn2 : (n : ℝ) ^ 2 * C / 2 + (n : ℝ) + 1 ≤ K := by
    have h3 : (n : ℝ) ^ 2 * C / 2 ≤ (n : ℝ) ^ 2 * C := by
      nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) hC.le]
    linarith
  have hKnC2 : (n : ℝ) * C / 2 ≤ K := by nlinarith [hnC, hn0, hC.le]
  have hUnit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hAinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hUnit
  set u : Fin (n + 1) → ℝ := fun k => A⁻¹ (Fin.last n) k with hu
  have hu_apply : ∀ k : Fin (n + 1), u k = A⁻¹ (Fin.last n) k := fun k => by rw [hu]
  have hu_ne : u ≠ 0 := by
    intro h0
    have h2 : (A⁻¹ * A) (Fin.last n) (Fin.last n) = 1 := by rw [hAinv]; simp
    rw [Matrix.mul_apply] at h2
    have hz : ∀ j : Fin (n + 1), A⁻¹ (Fin.last n) j * A j (Fin.last n) = 0 := by
      intro j
      have huj : u j = 0 := by rw [h0]; rfl
      rw [← hu_apply j, huj, zero_mul]
    rw [Finset.sum_eq_zero (fun j _ => hz j)] at h2
    exact one_ne_zero h2.symm
  obtain ⟨p, -, hp⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin (n + 1))) (fun k => |u k|)
      Finset.univ_nonempty
  have hup : u p ≠ 0 := by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hu_ne
    have h1 : 0 < |u k| := abs_pos.mpr hk
    exact abs_ne_zero.mp (ne_of_gt (lt_of_lt_of_le h1 (hp k (Finset.mem_univ k))))
  set β' : Fin n → ℝ := fun a => -(u (Fin.succAbove p a) / u p) with hβ'
  have hβ'le : ∀ a : Fin n, |β' a| ≤ 1 := by
    intro a
    rw [hβ', abs_neg, abs_div, div_le_one (abs_pos.mpr hup)]
    exact hp (Fin.succAbove p a) (Finset.mem_univ _)
  have hrel : ∀ b : Fin n,
      ∑ a : Fin n, β' a * A (Fin.succAbove p a) (Fin.castSucc b) = A p (Fin.castSucc b) := by
    intro b
    have huA : ∑ m : Fin (n + 1), u m * A m (Fin.castSucc b) = 0 := by
      have h1 : (A⁻¹ * A) (Fin.last n) (Fin.castSucc b) = 0 := by
        rw [hAinv, Matrix.one_apply]
        have hne : ¬ (Fin.last n = Fin.castSucc b) := fun h => Fin.castSucc_ne_last b h.symm
        rw [if_neg hne]
      rw [Matrix.mul_apply] at h1
      rw [show (∑ j : Fin (n + 1), A⁻¹ (Fin.last n) j * A j (Fin.castSucc b))
            = ∑ j : Fin (n + 1), u j * A j (Fin.castSucc b) from by
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [hu_apply j]] at h1
      exact h1
    have hsplit := Fin.sum_univ_succAbove
      (fun m : Fin (n + 1) => u m * A m (Fin.castSucc b)) p
    have h2 : ∑ a : Fin n, u (Fin.succAbove p a) * A (Fin.succAbove p a) (Fin.castSucc b)
        = -(u p * A p (Fin.castSucc b)) := by linarith
    calc ∑ a : Fin n, β' a * A (Fin.succAbove p a) (Fin.castSucc b)
        = ∑ a : Fin n,
            (-(u (Fin.succAbove p a) / u p)) * A (Fin.succAbove p a) (Fin.castSucc b) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hβ']
      _ = -(1 / u p) * ∑ a : Fin n,
            u (Fin.succAbove p a) * A (Fin.succAbove p a) (Fin.castSucc b) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro a _
            ring_nf
      _ = -(1 / u p) * (-(u p * A p (Fin.castSucc b))) := by rw [h2]
      _ = A p (Fin.castSucc b) := by
            field_simp
  have hA'det0 : (A.submatrix (Fin.succAbove p) Fin.castSucc).det ≠ 0 :=
    submatrix_succAbove_castSucc_det_ne_zero A hA p β' hrel
  set A' : Matrix (Fin n) (Fin n) ℝ := A.submatrix (Fin.succAbove p) Fin.castSucc with hA'set
  have hA'e : A' = A.submatrix (Fin.succAbove p) Fin.castSucc := hA'set
  have hA'det : A'.det ≠ 0 := by rw [hA'e]; exact hA'det0
  set lam' : Fin n → ℝ := fun a => lam (Fin.castSucc a) with hlam'set
  have hlam'e : lam' = fun a => lam (Fin.castSucc a) := hlam'set
  have hpos' : ∀ j : Fin n, 0 < lam' j := by intro j; rw [hlam'e]; exact hpos _
  have hmono' : ∀ i j : Fin n, i ≤ j → lam' i ≤ lam' j := by
    intro i j hij
    rw [hlam'e]
    exact hmono _ _ (Fin.castSucc_le_castSucc_iff.mpr hij)
  have hbnd' : ∀ i j : Fin n, |A' i j| ≤ lam' j := by
    intro i j
    rw [hA'e, hlam'e, Matrix.submatrix_apply]
    exact hbnd _ _
  obtain ⟨U', π', hU'diag, hU'tri, hU'bd⟩ := ih A' hA'det lam' hpos' hmono' hbnd'
  set UR : Matrix (Fin n) (Fin n) ℝ := U'.map (Int.castRingHom ℝ) with hURset
  have hURe : UR = U'.map (Int.castRingHom ℝ) := hURset
  have hURapp : ∀ i j : Fin n, UR i j = (U' i j : ℝ) := by
    intro i j; rw [hURe, Matrix.map_apply]; rfl
  set G : Matrix (Fin n) (Fin n) ℝ := A' * UR with hGset
  have hGe : G = A' * UR := hGset
  have hGdet : G.det ≠ 0 := by
    rw [hGe, Matrix.det_mul]
    have hURdet : UR.det = 1 := by
      rw [hURe]; exact det_map_intCast_of_unitriangular U' hU'diag hU'tri
    rw [hURdet, mul_one]
    exact hA'det
  have hGapp : ∀ i j : Fin n, G i j = ∑ k : Fin n, A' i k * (U' k j : ℝ) := by
    intro i j
    rw [hGe, Matrix.mul_apply]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [hURapp]
  set b : Fin n → ℝ := fun a => A (Fin.succAbove p a) (Fin.last n) with hbset
  have hbe : b = fun a => A (Fin.succAbove p a) (Fin.last n) := hbset
  have hbnd_b : ∀ a : Fin n, |b a| ≤ lam (Fin.last n) := by
    intro a; rw [hbe]; exact hbnd _ _
  set γ : Fin n → ℝ := fun j => ∑ i : Fin n, (G⁻¹) j i * b i with hγset
  have hγe : γ = fun j => ∑ i : Fin n, (G⁻¹) j i * b i := hγset
  have hGγ : ∀ a : Fin n, ∑ j : Fin n, G a j * γ j = b a := by
    intro a
    have hGG : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hGdet)
    calc ∑ j : Fin n, G a j * γ j
        = ∑ j : Fin n, G a j * (∑ i : Fin n, (G⁻¹) j i * b i) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [hγe]
      _ = ∑ j : Fin n, ∑ i : Fin n, (G a j * (G⁻¹) j i) * b i := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
      _ = ∑ i : Fin n, (∑ j : Fin n, G a j * (G⁻¹) j i) * b i := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Finset.sum_mul]
      _ = ∑ i : Fin n, (G * G⁻¹) a i * b i := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Matrix.mul_apply]
      _ = ∑ i : Fin n, (1 : Matrix (Fin n) (Fin n) ℝ) a i * b i := by rw [hGG]
      _ = b a := by
            rw [show (∑ i : Fin n, (1 : Matrix (Fin n) (Fin n) ℝ) a i * b i)
                = ∑ i : Fin n, (if a = i then (1 : ℝ) else 0) * b i from by
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  rw [Matrix.one_apply]]
            rw [show (∑ i : Fin n, (if a = i then (1 : ℝ) else 0) * b i)
                = ∑ i : Fin n, (if a = i then b i else 0) from by
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  by_cases h : a = i <;> simp [h]]
            rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ a)]
  have hξ : ∀ j : Fin n, ∃ z : ℤ, |(z : ℝ) + γ j| ≤ 1 / 2 := by
    intro j
    obtain ⟨z, hz⟩ := exists_int_abs_sub_le_half (- γ j)
    refine ⟨z, ?_⟩
    rw [show (- γ j - (z : ℝ)) = -(z + γ j) from by ring, abs_neg] at hz
    exact hz
  set ξ : Fin n → ℤ := fun j => Classical.choose (hξ j) with hξset
  have hξspec : ∀ j : Fin n, |((ξ j : ℤ) : ℝ) + γ j| ≤ 1 / 2 :=
    fun j => Classical.choose_spec (hξ j)
  set U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := fun k j =>
    Fin.lastCases (motive := fun _ => ℤ)
      (Fin.lastCases (motive := fun _ => ℤ) 1 (fun k' => ∑ a : Fin n, ξ a * U' k' a) k)
      (fun j' => Fin.lastCases (motive := fun _ => ℤ) 0 (fun k' => U' k' j') k)
      j with hUset
  have hUe : U = fun k j =>
    Fin.lastCases (motive := fun _ => ℤ)
      (Fin.lastCases (motive := fun _ => ℤ) 1 (fun k' => ∑ a : Fin n, ξ a * U' k' a) k)
      (fun j' => Fin.lastCases (motive := fun _ => ℤ) 0 (fun k' => U' k' j') k)
      j := hUset
  have hUcc : ∀ k' j' : Fin n, U (Fin.castSucc k') (Fin.castSucc j') = U' k' j' := by
    intro k' j'; rw [hUe]; simp [Fin.lastCases_castSucc]
  have hUcl : ∀ k' : Fin n, U (Fin.castSucc k') (Fin.last n) = ∑ a : Fin n, ξ a * U' k' a := by
    intro k'; rw [hUe]; simp [Fin.lastCases_castSucc, Fin.lastCases_last]
  have hUlc : ∀ j' : Fin n, U (Fin.last n) (Fin.castSucc j') = 0 := by
    intro j'; rw [hUe]; simp [Fin.lastCases_castSucc, Fin.lastCases_last]
  have hUll : U (Fin.last n) (Fin.last n) = 1 := by rw [hUe]; simp [Fin.lastCases_last]
  have hUdiag : ∀ i : Fin (n + 1), U i i = 1 := by
    intro i
    refine Fin.lastCases (motive := fun i => U i i = 1) ?_ ?_ i
    · rw [hUll]
    · intro i'; rw [hUcc]; exact hU'diag i'
  have hUtri : ∀ i j : Fin (n + 1), j < i → U i j = 0 := by
    intro i
    induction i using Fin.lastCases with
    | last =>
        intro j hji
        induction j using Fin.lastCases with
        | last => exact absurd hji (lt_irrefl _)
        | cast j' => exact hUlc j'
    | cast i' =>
        intro j hji
        induction j using Fin.lastCases with
        | last => exact absurd hji (not_lt.mpr (le_of_lt (Fin.castSucc_lt_last i')))
        | cast j' =>
            rw [hUcc]
            exact hU'tri i' j' (Fin.castSucc_lt_castSucc_iff.mp hji)
  set Psi : Fin (n + 1) → Fin (n + 1) := fun i =>
    Fin.lastCases (motive := fun _ => Fin (n + 1)) p (fun a => Fin.succAbove p (π' a)) i
    with hPsiset
  have hPsie : Psi = fun i =>
    Fin.lastCases (motive := fun _ => Fin (n + 1)) p (fun a => Fin.succAbove p (π' a)) i := hPsiset
  have hPsi_last : Psi (Fin.last n) = p := by rw [hPsie]; simp [Fin.lastCases_last]
  have hPsi_cast : ∀ a : Fin n, Psi (Fin.castSucc a) = Fin.succAbove p (π' a) := by
    intro a; rw [hPsie]; simp [Fin.lastCases_castSucc]
  have hPsi_inj : Function.Injective Psi := by
    have key : ∀ i j : Fin (n + 1), Psi i = Psi j → i = j := by
      intro i
      refine Fin.lastCases (motive := fun i => ∀ j, Psi i = Psi j → i = j) ?_ ?_ i
      · intro j
        refine Fin.lastCases (motive := fun j => Psi (Fin.last n) = Psi j → Fin.last n = j) ?_ ?_ j
        · intro _; rfl
        · intro b h
          exfalso
          rw [hPsi_last, hPsi_cast b] at h
          exact Fin.succAbove_ne p (π' b) h.symm
      · intro a j
        refine Fin.lastCases (motive := fun j => Psi (Fin.castSucc a) = Psi j → Fin.castSucc a = j)
          ?_ ?_ j
        · intro h
          exfalso
          rw [hPsi_last, hPsi_cast a] at h
          exact Fin.succAbove_ne p (π' a) h
        · intro b h
          rw [hPsi_cast a, hPsi_cast b] at h
          have h3 : π' a = π' b := Fin.succAbove_right_injective h
          rw [π'.injective h3]
    intro i j hij
    exact key i j hij
  set π : Equiv.Perm (Fin (n + 1)) := Equiv.ofBijective Psi hPsi_inj.bijective_of_finite with hπset
  have hπe : π = Equiv.ofBijective Psi hPsi_inj.bijective_of_finite := hπset
  have hπ_last : π (Fin.last n) = p := by
    rw [hπe]; simp [Equiv.ofBijective_apply, hPsi_last]
  have hπ_cast : ∀ a : Fin n, π (Fin.castSucc a) = Fin.succAbove p (π' a) := by
    intro a; rw [hπe]; simp [Equiv.ofBijective_apply, hPsi_cast a]
  set Um : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := U.map (Int.castRingHom ℝ) with hUmset
  have hUme : Um = U.map (Int.castRingHom ℝ) := hUmset
  set ν : Fin n → ℝ := fun j => ((ξ j : ℤ) : ℝ) + γ j with hνset
  have hνe : ν = fun j => ((ξ j : ℤ) : ℝ) + γ j := hνset
  have hν_le : ∀ j : Fin n, |ν j| ≤ 1 / 2 := by intro j; rw [hνe]; exact hξspec j
  have hlam'le : ∀ j : Fin n, lam' j ≤ lam (Fin.last n) := by
    intro j; rw [hlam'e]; exact hmono _ _ (le_of_lt (Fin.castSucc_lt_last j))
  have hGmin : ∀ i j : Fin n, |G (π' i) j| ≤ C * min (lam' i) (lam' j) := by
    intro i j; rw [hGapp]; exact hU'bd i j
  have hGbdj : ∀ a j : Fin n, |G a j| ≤ C * lam' j := by
    intro a j
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (min_le_right (lam' (π'.symm a)) (lam' j)) hC.le)
    simpa [Equiv.apply_symm_apply] using hGmin (π'.symm a) j
  have hGνN : ∀ a : Fin n, |∑ j : Fin n, G a j * ν j| ≤ (n : ℝ) * C * lam (Fin.last n) / 2 := by
    intro a
    calc |∑ j : Fin n, G a j * ν j|
        ≤ ∑ j : Fin n, |G a j * ν j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |G a j| * |ν j| := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [abs_mul]
      _ ≤ ∑ _j : Fin n, (C * lam (Fin.last n)) * (1 / 2) := by
            refine Finset.sum_le_sum ?_
            intro j _
            refine mul_le_mul (le_trans (hGbdj a j) (mul_le_mul_of_nonneg_left (hlam'le j) hC.le))
              (hν_le j) (abs_nonneg _) ?_
            exact mul_nonneg hC.le (le_of_lt (hpos _))
      _ = (n : ℝ) * ((C * lam (Fin.last n)) * (1 / 2)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (n : ℝ) * C * lam (Fin.last n) / 2 := by ring
  have hGνπ : ∀ i : Fin n, |∑ j : Fin n, G (π' i) j * ν j| ≤ (n : ℝ) * C * lam' i / 2 := by
    intro i
    calc |∑ j : Fin n, G (π' i) j * ν j|
        ≤ ∑ j : Fin n, |G (π' i) j * ν j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |G (π' i) j| * |ν j| := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [abs_mul]
      _ ≤ ∑ _j : Fin n, (C * lam' i) * (1 / 2) := by
            refine Finset.sum_le_sum ?_
            intro j _
            refine mul_le_mul ?_ (hν_le j) (abs_nonneg _) ?_
            · exact le_trans (hGmin i j) (mul_le_mul_of_nonneg_left (min_le_left _ _) hC.le)
            · exact mul_nonneg hC.le (le_of_lt (hpos' i))
      _ = (n : ℝ) * ((C * lam' i) * (1 / 2)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (n : ℝ) * C * lam' i / 2 := by ring
  have hAapply : ∀ k j : Fin (n + 1), (A * Um) k j = ∑ i : Fin (n + 1), A k i * (U i j : ℝ) := by
    intro k j
    rw [hUme, Matrix.mul_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Matrix.map_apply]
    rfl
  have h1b : ∀ a j' : Fin n,
      (A * Um) (Fin.succAbove p a) (Fin.castSucc j') = G a j' := by
    intro a j'
    rw [hAapply, Fin.sum_univ_castSucc]
    rw [show (∑ x : Fin n, A (Fin.succAbove p a) (Fin.castSucc x) *
              (U (Fin.castSucc x) (Fin.castSucc j') : ℝ))
        = ∑ x : Fin n, A (Fin.succAbove p a) (Fin.castSucc x) * (U' x j' : ℝ) from by
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [hUcc]]
    rw [show A (Fin.succAbove p a) (Fin.last n) * (U (Fin.last n) (Fin.castSucc j') : ℝ)
        = 0 from by rw [hUlc, Int.cast_zero, mul_zero]]
    rw [add_zero, hGapp]
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [hA'e, Matrix.submatrix_apply]
  have h2b : ∀ a : Fin n,
      (A * Um) (Fin.succAbove p a) (Fin.last n) = ∑ j : Fin n, G a j * ν j := by
    intro a
    have step : ∑ x : Fin n, A (Fin.succAbove p a) (Fin.castSucc x) *
          ((∑ y : Fin n, ξ y * U' x y : ℤ) : ℝ)
        = ∑ j : Fin n, G a j * ((ξ j : ℤ) : ℝ) := by
      calc ∑ x : Fin n, A (Fin.succAbove p a) (Fin.castSucc x) *
            ((∑ y : Fin n, ξ y * U' x y : ℤ) : ℝ)
          = ∑ x : Fin n, ∑ y : Fin n, A (Fin.succAbove p a) (Fin.castSucc x) *
              ((ξ y : ℤ) : ℝ) * (U' x y : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro x _
              push_cast
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro y _
              ring
        _ = ∑ y : Fin n, ∑ x : Fin n, A (Fin.succAbove p a) (Fin.castSucc x) *
              ((ξ y : ℤ) : ℝ) * (U' x y : ℝ) := Finset.sum_comm
        _ = ∑ y : Fin n, (∑ x : Fin n, A (Fin.succAbove p a) (Fin.castSucc x) *
              (U' x y : ℝ)) * ((ξ y : ℤ) : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro y _
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl ?_
              intro x _
              ring
        _ = ∑ y : Fin n, G a y * ((ξ y : ℤ) : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro y _
              rw [hGapp]
              congr 1
    rw [hAapply, Fin.sum_univ_castSucc]
    rw [show (∑ x : Fin n, A (Fin.succAbove p a) (Fin.castSucc x) *
              (U (Fin.castSucc x) (Fin.last n) : ℝ))
        = ∑ x : Fin n, A (Fin.succAbove p a) (Fin.castSucc x) *
              ((∑ y : Fin n, ξ y * U' x y : ℤ) : ℝ) from by
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [hUcl]]
    rw [show A (Fin.succAbove p a) (Fin.last n) * (U (Fin.last n) (Fin.last n) : ℝ) = b a from by
          rw [hUll, Int.cast_one, mul_one, hbe]]
    rw [step, ← hGγ a]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hνe, mul_add]
  have h3b : ∀ j' : Fin n, (A * Um) p (Fin.castSucc j') = ∑ a : Fin n, β' a * G a j' := by
    intro j'
    rw [hAapply, Fin.sum_univ_castSucc]
    rw [show (∑ x : Fin n, A p (Fin.castSucc x) * (U (Fin.castSucc x) (Fin.castSucc j') : ℝ))
        = ∑ x : Fin n, A p (Fin.castSucc x) * (U' x j' : ℝ) from by
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [hUcc]]
    rw [show A p (Fin.last n) * (U (Fin.last n) (Fin.castSucc j') : ℝ) = 0 from by
          rw [hUlc, Int.cast_zero, mul_zero]]
    rw [add_zero]
    calc ∑ x : Fin n, A p (Fin.castSucc x) * (U' x j' : ℝ)
        = ∑ x : Fin n,
            (∑ a : Fin n, β' a * A (Fin.succAbove p a) (Fin.castSucc x)) * (U' x j' : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [← hrel x]
      _ = ∑ x : Fin n, ∑ a : Fin n,
            (β' a * A (Fin.succAbove p a) (Fin.castSucc x)) * (U' x j' : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [Finset.sum_mul]
      _ = ∑ a : Fin n, ∑ x : Fin n,
            (β' a * A (Fin.succAbove p a) (Fin.castSucc x)) * (U' x j' : ℝ) := Finset.sum_comm
      _ = ∑ a : Fin n, β' a * G a j' := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hGapp, Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [hA'e, Matrix.submatrix_apply]
            ring
  have h4b : (A * Um) p (Fin.last n)
      = (∑ a : Fin n, β' a * (∑ j : Fin n, G a j * ν j))
        - (∑ a : Fin n, β' a * b a) + A p (Fin.last n) := by
    rw [hAapply, Fin.sum_univ_castSucc]
    rw [show (∑ x : Fin n, A p (Fin.castSucc x) * (U (Fin.castSucc x) (Fin.last n) : ℝ))
        = ∑ x : Fin n, A p (Fin.castSucc x) * ((∑ y : Fin n, ξ y * U' x y : ℤ) : ℝ) from by
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [hUcl]]
    rw [show A p (Fin.last n) * (U (Fin.last n) (Fin.last n) : ℝ) = A p (Fin.last n) from by
          rw [hUll, Int.cast_one, mul_one]]
    have step : ∑ x : Fin n, A p (Fin.castSucc x) * ((∑ y : Fin n, ξ y * U' x y : ℤ) : ℝ)
        = ∑ a : Fin n, β' a * (∑ j : Fin n, G a j * ((ξ j : ℤ) : ℝ)) := by
      calc ∑ x : Fin n, A p (Fin.castSucc x) * ((∑ y : Fin n, ξ y * U' x y : ℤ) : ℝ)
          = ∑ x : Fin n, (∑ a : Fin n, β' a * A (Fin.succAbove p a) (Fin.castSucc x)) *
              ((∑ y : Fin n, ξ y * U' x y : ℤ) : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro x _
              rw [← hrel x]
        _ = ∑ x : Fin n, ∑ a : Fin n, (β' a * A (Fin.succAbove p a) (Fin.castSucc x)) *
              ((∑ y : Fin n, ξ y * U' x y : ℤ) : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro x _
              rw [Finset.sum_mul]
        _ = ∑ a : Fin n, ∑ x : Fin n, (β' a * A (Fin.succAbove p a) (Fin.castSucc x)) *
              ((∑ y : Fin n, ξ y * U' x y : ℤ) : ℝ) := Finset.sum_comm
        _ = ∑ a : Fin n, β' a * (∑ j : Fin n, G a j * ((ξ j : ℤ) : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              rw [show (∑ x : Fin n, (β' a * A (Fin.succAbove p a) (Fin.castSucc x)) *
                    ((∑ y : Fin n, ξ y * U' x y : ℤ) : ℝ))
                  = β' a * ∑ x : Fin n, A (Fin.succAbove p a) (Fin.castSucc x) *
                    ((∑ y : Fin n, ξ y * U' x y : ℤ) : ℝ) from by
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl ?_
                    intro x _
                    ring]
              congr 1
              calc ∑ x : Fin n, A (Fin.succAbove p a) (Fin.castSucc x) *
                    ((∑ y : Fin n, ξ y * U' x y : ℤ) : ℝ)
                  = ∑ x : Fin n, ∑ y : Fin n, A (Fin.succAbove p a) (Fin.castSucc x) *
                      ((ξ y : ℤ) : ℝ) * (U' x y : ℝ) := by
                      refine Finset.sum_congr rfl ?_
                      intro x _
                      push_cast
                      rw [Finset.mul_sum]
                      refine Finset.sum_congr rfl ?_
                      intro y _
                      ring
                _ = ∑ y : Fin n, ∑ x : Fin n, A (Fin.succAbove p a) (Fin.castSucc x) *
                      ((ξ y : ℤ) : ℝ) * (U' x y : ℝ) := Finset.sum_comm
                _ = ∑ y : Fin n, (∑ x : Fin n, A (Fin.succAbove p a) (Fin.castSucc x) *
                      (U' x y : ℝ)) * ((ξ y : ℤ) : ℝ) := by
                      refine Finset.sum_congr rfl ?_
                      intro y _
                      rw [Finset.sum_mul]
                      refine Finset.sum_congr rfl ?_
                      intro x _
                      ring
                _ = ∑ y : Fin n, G a y * ((ξ y : ℤ) : ℝ) := by
                      refine Finset.sum_congr rfl ?_
                      intro y _
                      rw [hGapp]
                      congr 1
    rw [step]
    have heq : ∀ a : Fin n, ∑ j : Fin n, G a j * ν j
        = (∑ j : Fin n, G a j * ((ξ j : ℤ) : ℝ)) + b a := by
      intro a
      calc ∑ j : Fin n, G a j * ν j
          = ∑ j : Fin n, G a j * (((ξ j : ℤ) : ℝ) + γ j) := by rw [hνe]
        _ = ∑ j : Fin n, (G a j * ((ξ j : ℤ) : ℝ) + G a j * γ j) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [mul_add]
        _ = (∑ j : Fin n, G a j * ((ξ j : ℤ) : ℝ)) + ∑ j : Fin n, G a j * γ j :=
              Finset.sum_add_distrib
        _ = (∑ j : Fin n, G a j * ((ξ j : ℤ) : ℝ)) + b a := by rw [← hGγ a]
    have hsplit : ∑ a : Fin n, β' a * (∑ j : Fin n, G a j * ν j)
        = (∑ a : Fin n, β' a * (∑ j : Fin n, G a j * ((ξ j : ℤ) : ℝ)))
          + ∑ a : Fin n, β' a * b a := by
      rw [Finset.sum_congr rfl (fun a _ => by rw [heq a, mul_add]), Finset.sum_add_distrib]
    rw [hsplit]
    ring
  refine ⟨U, π, hUdiag, hUtri, ?_⟩
  intro i j
  have hconv : (∑ k : Fin (n + 1), A (π i) k * (U k j : ℝ)) = (A * Um) (π i) j := by
    rw [hAapply]
  rw [hconv]
  refine Fin.lastCases (motive := fun i => |(A * Um) (π i) j| ≤ K * min (lam i) (lam j))
    ?_ ?_ i
  · rw [hπ_last]
    refine Fin.lastCases (motive := fun j =>
      |(A * Um) p j| ≤ K * min (lam (Fin.last n)) (lam j)) ?_ ?_ j
    · rw [h4b, min_self]
      have hS : |∑ a : Fin n, β' a * (∑ j : Fin n, G a j * ν j)|
          ≤ (n : ℝ) * ((n : ℝ) * C * lam (Fin.last n) / 2) := by
        calc |∑ a : Fin n, β' a * (∑ j : Fin n, G a j * ν j)|
            ≤ ∑ a : Fin n, |β' a * (∑ j : Fin n, G a j * ν j)| :=
                Finset.abs_sum_le_sum_abs _ _
          _ = ∑ a : Fin n, |β' a| * |∑ j : Fin n, G a j * ν j| := by
                refine Finset.sum_congr rfl ?_
                intro a _
                rw [abs_mul]
          _ ≤ ∑ _a : Fin n, 1 * ((n : ℝ) * C * lam (Fin.last n) / 2) := by
                refine Finset.sum_le_sum ?_
                intro a _
                refine mul_le_mul (hβ'le a) (hGνN a) (abs_nonneg _) (by norm_num)
          _ = (n : ℝ) * ((n : ℝ) * C * lam (Fin.last n) / 2) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                ring
      have hT : |∑ a : Fin n, β' a * b a| ≤ (n : ℝ) * lam (Fin.last n) := by
        calc |∑ a : Fin n, β' a * b a|
            ≤ ∑ a : Fin n, |β' a * b a| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ a : Fin n, |β' a| * |b a| := by
                refine Finset.sum_congr rfl ?_
                intro a _
                rw [abs_mul]
          _ ≤ ∑ _a : Fin n, 1 * lam (Fin.last n) := by
                refine Finset.sum_le_sum ?_
                intro a _
                refine mul_le_mul (hβ'le a) (hbnd_b a) (abs_nonneg _) (by norm_num)
          _ = (n : ℝ) * lam (Fin.last n) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                ring
      have hApl : |A p (Fin.last n)| ≤ lam (Fin.last n) := hbnd _ _
      have hST : |(∑ a : Fin n, β' a * (∑ j : Fin n, G a j * ν j))
            - (∑ a : Fin n, β' a * b a)|
          ≤ (n : ℝ) * ((n : ℝ) * C * lam (Fin.last n) / 2) + (n : ℝ) * lam (Fin.last n) := by
        rw [sub_eq_add_neg]
        calc |(∑ a : Fin n, β' a * (∑ j : Fin n, G a j * ν j))
              + -(∑ a : Fin n, β' a * b a)|
            ≤ |∑ a : Fin n, β' a * (∑ j : Fin n, G a j * ν j)|
              + |-(∑ a : Fin n, β' a * b a)| := abs_add_le _ _
          _ = |∑ a : Fin n, β' a * (∑ j : Fin n, G a j * ν j)|
              + |∑ a : Fin n, β' a * b a| := by rw [abs_neg]
          _ ≤ _ := by linarith [hS, hT]
      have hsum : |(∑ a : Fin n, β' a * (∑ j : Fin n, G a j * ν j))
            - (∑ a : Fin n, β' a * b a) + A p (Fin.last n)|
          ≤ ((n : ℝ) * ((n : ℝ) * C * lam (Fin.last n) / 2) + (n : ℝ) * lam (Fin.last n))
            + lam (Fin.last n) := by
        calc |((∑ a : Fin n, β' a * (∑ j : Fin n, G a j * ν j))
              - (∑ a : Fin n, β' a * b a)) + A p (Fin.last n)|
            ≤ |(∑ a : Fin n, β' a * (∑ j : Fin n, G a j * ν j))
              - (∑ a : Fin n, β' a * b a)| + |A p (Fin.last n)| := abs_add_le _ _
          _ ≤ _ := by linarith [hST, hApl]
      have hfin : (n : ℝ) * ((n : ℝ) * C * lam (Fin.last n) / 2)
            + (n : ℝ) * lam (Fin.last n) + lam (Fin.last n) ≤ K * lam (Fin.last n) := by
        have h3 : (n : ℝ) * ((n : ℝ) * C * lam (Fin.last n) / 2)
            + (n : ℝ) * lam (Fin.last n) + lam (Fin.last n)
            = ((n : ℝ) ^ 2 * C / 2 + (n : ℝ) + 1) * lam (Fin.last n) := by ring
        rw [h3]
        exact mul_le_mul_of_nonneg_right hKn2 (le_of_lt (hpos _))
      linarith
    · intro j'
      rw [h3b]
      have hS : |∑ a : Fin n, β' a * G a j'| ≤ (n : ℝ) * C * lam' j' := by
        calc |∑ a : Fin n, β' a * G a j'|
            ≤ ∑ a : Fin n, |β' a * G a j'| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ a : Fin n, |β' a| * |G a j'| := by
                refine Finset.sum_congr rfl ?_
                intro a _
                rw [abs_mul]
          _ ≤ ∑ _a : Fin n, 1 * (C * lam' j') := by
                refine Finset.sum_le_sum ?_
                intro a _
                refine mul_le_mul (hβ'le a) (hGbdj a j') (abs_nonneg _) (by norm_num)
          _ = (n : ℝ) * (C * lam' j') := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                ring
          _ = (n : ℝ) * C * lam' j' := by ring
      have hmin : min (lam (Fin.last n)) (lam (Fin.castSucc j')) = lam' j' := by
        rw [hlam'e, min_eq_right]
        exact hmono _ _ (le_of_lt (Fin.castSucc_lt_last j'))
      rw [hmin]
      have hfin : (n : ℝ) * C * lam' j' ≤ K * lam' j' :=
        mul_le_mul_of_nonneg_right hnC (le_of_lt (hpos' j'))
      linarith
  · intro i'
    rw [hπ_cast i']
    refine Fin.lastCases (motive := fun j =>
      |(A * Um) (Fin.succAbove p (π' i')) j|
        ≤ K * min (lam (Fin.castSucc i')) (lam j)) ?_ ?_ j
    · rw [h2b]
      have hS := hGνπ i'
      have hmin : min (lam (Fin.castSucc i')) (lam (Fin.last n)) = lam' i' := by
        rw [hlam'e, min_eq_left]
        exact hmono _ _ (le_of_lt (Fin.castSucc_lt_last i'))
      rw [hmin]
      have hfin : (n : ℝ) * C * lam' i' / 2 ≤ K * lam' i' := by
        calc (n : ℝ) * C * lam' i' / 2 = ((n : ℝ) * C / 2) * lam' i' := by ring
          _ ≤ K * lam' i' := mul_le_mul_of_nonneg_right hKnC2 (le_of_lt (hpos' i'))
      linarith
    · intro j'
      rw [h1b]
      have hmin : min (lam (Fin.castSucc i')) (lam (Fin.castSucc j')) = min (lam' i') (lam' j') := by
        rw [hlam'e]
      rw [hmin, hGapp]
      refine le_trans (hU'bd i' j') ?_
      exact mul_le_mul_of_nonneg_right hK1 (le_of_lt (lt_min (hpos' i') (hpos' j')))





theorem gb_matrix : ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ GB N C := by
  intro N
  induction N with
  | zero => exact ⟨1, one_pos, GB_zero⟩
  | succ n ih =>
      obtain ⟨C, hC, hgb⟩ := ih
      exact ⟨max C ((n : ℝ) ^ 2 * C + (n : ℝ) + 1),
        lt_of_lt_of_le hC (le_max_left _ _), GB_succ hC hgb⟩

theorem graded_basis_real {N : ℕ} (hN : 1 ≤ N) (M : Matrix (Fin N) (Fin N) ℝ) (hM : M.det ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : ℝ) (hQ : 1 ≤ Q) (c : Fin N → ℝ) (lam : Fin N → ℝ) (x : Fin N → Fin N → ℤ),
        (∀ j, 0 < lam j) →
        (∀ i j, i ≤ j → lam i ≤ lam j) →
        (∀ j, x j ≠ 0) →
        (LinearIndependent ℚ (fun j => fun k => (x j k : ℚ))) →
        (∀ j i, |∑ k, M i k * ((x j k : ℝ))| ≤ lam j * Q ^ (c i)) →
        (∀ j, ∀ t : ℝ, 0 < t → t < lam j → ∀ y : Fin N → ℤ,
            (∀ i, |∑ k, M i k * ((y k : ℝ))| ≤ t * Q ^ (c i)) →
            (fun k => (y k : ℚ)) ∈
              Submodule.span ℚ (Set.range (fun i : {i : Fin N // i < j} =>
                fun k => (x i.1 k : ℚ)))) →
        ∃ (ξ : Fin N → Fin N → ℤ) (π : Equiv.Perm (Fin N)),
          (∀ i j, j ≤ i → ξ i j = 0) ∧
          ∀ t j, |∑ k, M (π t) k *
              (((x j k : ℝ)) + ∑ i : Fin N, ((ξ i j : ℤ) : ℝ) * ((x i k : ℝ)))| ≤
              C * min (lam t) (lam j) * Q ^ (c (π t)) := by
  obtain ⟨C, hCpos, hgb⟩ := gb_matrix N
  refine ⟨C, hCpos, ?_⟩
  intro Q hQ c lam x hpos hmono hxne hind hbnd hgrade
  have hQpos : 0 < Q := lt_of_lt_of_le one_pos hQ
  have hQpow : ∀ i : Fin N, 0 < Q ^ (c i) := fun i => Real.rpow_pos_of_pos hQpos _
  set A : Matrix (Fin N) (Fin N) ℝ := fun i j => (∑ k, M i k * (x j k : ℝ)) / Q ^ (c i)
    with hAset
  have hAeq : ∀ i j : Fin N, A i j = (∑ k, M i k * (x j k : ℝ)) / Q ^ (c i) := by
    intro i j; rw [hAset]
  have hAbd : ∀ i j : Fin N, |A i j| ≤ lam j := by
    intro i j
    rw [hAeq i j, abs_div, abs_of_pos (hQpow i), div_le_iff₀ (hQpow i)]
    exact hbnd j i
  have hdetA : A.det ≠ 0 := by
    set Uq : Matrix (Fin N) (Fin N) ℚ := fun k j => (x j k : ℚ) with hUqset
    have hUqe : Uq = fun k j => (x j k : ℚ) := hUqset
    have hind' : LinearIndependent ℚ Uq.col := by
      rw [hUqe]; exact hind
    have hUdet : Uq.det ≠ 0 :=
      Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.linearIndependent_col_iff.mp hind')
    set X : Matrix (Fin N) (Fin N) ℝ := Uq.map (Rat.castHom ℝ) with hXset
    have hXe : X = Uq.map (Rat.castHom ℝ) := hXset
    have hXapp : ∀ k j : Fin N, X k j = (x j k : ℝ) := by
      intro k j
      rw [hXe, Matrix.map_apply, hUqe]
      simp
    have hXdet : X.det ≠ 0 := by
      rw [hXe]
      have hkey : (Uq.map (Rat.castHom ℝ)).det = ((Uq.det : ℚ) : ℝ) := by
        rw [show Uq.map ⇑(Rat.castHom ℝ) = (Rat.castHom ℝ).mapMatrix Uq from rfl]
        rw [← RingHom.map_det]; rfl
      rw [hkey]
      intro h
      refine hUdet (Rat.cast_injective (α := ℝ) ?_)
      simpa using h
    set D : Matrix (Fin N) (Fin N) ℝ := Matrix.diagonal (fun i => (Q ^ (c i))⁻¹) with hDset
    have hDe : D = Matrix.diagonal (fun i => (Q ^ (c i))⁻¹) := hDset
    have hDdet : D.det ≠ 0 := by
      rw [hDe, Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => inv_ne_zero (ne_of_gt (hQpow i)))
    have hRHS : ∀ i j : Fin N, (D * (M * X)) i j
        = (∑ k, M i k * (x j k : ℝ)) / Q ^ (c i) := by
      intro i j
      rw [hDe, Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [Matrix.diagonal_apply_eq, Matrix.mul_apply,
            Finset.sum_congr rfl (fun k _ => by rw [hXapp k j]), div_eq_mul_inv]
        ring
      · intro b _ hb
        rw [Matrix.diagonal_apply_ne _ (Ne.symm hb), zero_mul]
      · intro h; exact absurd (Finset.mem_univ i) h
    have hAdec : A = D * (M * X) := by
      ext i j
      rw [hAeq i j, hRHS i j]
    rw [hAdec, Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero hDdet (mul_ne_zero hM hXdet)
  obtain ⟨U, π, hUdiag, hUtri, hbd⟩ := hgb A hdetA lam hpos hmono hAbd
  set ξ : Fin N → Fin N → ℤ := fun i j => U i j - (if i = j then 1 else 0) with hξset
  have hξeq : ∀ i j : Fin N, ξ i j = U i j - (if i = j then 1 else 0) := by
    intro i j; rw [hξset]
  refine ⟨ξ, π, ?_, ?_⟩
  · intro i j hji
    rw [hξeq i j]
    by_cases hij : i = j
    · rw [if_pos hij, hij, hUdiag j, sub_self]
    · have hlt : j < i := lt_of_le_of_ne hji (Ne.symm hij)
      rw [if_neg hij, hUtri i j hlt, sub_zero]
  · intro t j
    have hcast : ∀ i : Fin N, ((ξ i j : ℤ) : ℝ)
        = (U i j : ℝ) - (if i = j then (1 : ℝ) else 0) := by
      intro i
      rw [hξeq i j]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij]
    have hstep : ∀ k : Fin N, (x j k : ℝ) + ∑ i, ((ξ i j : ℤ) : ℝ) * ((x i k : ℝ))
        = ∑ i, (U i j : ℝ) * ((x i k : ℝ)) := by
      intro k
      have h1 : ∑ i : Fin N, ((ξ i j : ℤ) : ℝ) * ((x i k : ℝ))
          = (∑ i : Fin N, (U i j : ℝ) * ((x i k : ℝ))) - (x j k : ℝ) := by
        rw [show (∑ i : Fin N, ((ξ i j : ℤ) : ℝ) * ((x i k : ℝ)))
              = ∑ i : Fin N, ((U i j : ℝ) - (if i = j then (1 : ℝ) else 0)) * ((x i k : ℝ))
            from Finset.sum_congr rfl (fun i _ => by rw [hcast i])]
        rw [show (∑ i : Fin N, ((U i j : ℝ) - (if i = j then (1 : ℝ) else 0)) * ((x i k : ℝ)))
              = ∑ i : Fin N, ((U i j : ℝ) * ((x i k : ℝ))
                - (if i = j then (1 : ℝ) else 0) * ((x i k : ℝ)))
            from Finset.sum_congr rfl (fun i _ => by ring)]
        rw [Finset.sum_sub_distrib]
        congr 1
        rw [Finset.sum_eq_single j]
        · rw [if_pos rfl, one_mul]
        · intro b _ hb; rw [if_neg hb, zero_mul]
        · intro h; exact absurd (Finset.mem_univ j) h
      rw [h1]; ring
    have hAQ : ∀ i : Fin N, A (π t) i * Q ^ (c (π t)) = ∑ k, M (π t) k * (x i k : ℝ) := by
      intro i
      rw [hAeq (π t) i, div_mul_cancel₀ _ (ne_of_gt (hQpow _))]
    have key : ∑ k, M (π t) k * ((x j k : ℝ) + ∑ i, ((ξ i j : ℤ) : ℝ) * ((x i k : ℝ)))
        = Q ^ (c (π t)) * ∑ i, A (π t) i * ((U i j : ℝ)) := by
      calc ∑ k, M (π t) k * ((x j k : ℝ) + ∑ i, ((ξ i j : ℤ) : ℝ) * ((x i k : ℝ)))
          = ∑ k, M (π t) k * (∑ i, (U i j : ℝ) * ((x i k : ℝ))) := by
              refine Finset.sum_congr rfl ?_
              intro k _
              rw [hstep k]
        _ = ∑ k, ∑ i, M (π t) k * ((U i j : ℝ) * ((x i k : ℝ))) := by
              refine Finset.sum_congr rfl ?_
              intro k _
              rw [Finset.mul_sum]
        _ = ∑ i, ∑ k, M (π t) k * ((U i j : ℝ) * ((x i k : ℝ))) := Finset.sum_comm
        _ = ∑ i, (U i j : ℝ) * ∑ k, M (π t) k * ((x i k : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro k _
              ring
        _ = ∑ i, (U i j : ℝ) * (A (π t) i * Q ^ (c (π t))) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [hAQ i]
        _ = Q ^ (c (π t)) * ∑ i, A (π t) i * ((U i j : ℝ)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i _
              ring
    rw [key, abs_mul, abs_of_pos (hQpow (π t))]
    calc Q ^ (c (π t)) * |∑ i, A (π t) i * ((U i j : ℝ))|
        ≤ Q ^ (c (π t)) * (C * min (lam t) (lam j)) :=
          mul_le_mul_of_nonneg_left (hbd t j) (le_of_lt (hQpow _))
      _ = C * min (lam t) (lam j) * Q ^ (c (π t)) := by ring

end Commons.NumberTheory.DiophantineApproximation