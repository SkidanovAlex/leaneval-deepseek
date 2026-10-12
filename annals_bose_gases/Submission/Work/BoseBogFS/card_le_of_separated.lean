import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A lattice (grid) packing bound for separated families in `ℝ³`

We prove `Work.BoseBogFS.card_le_of_separated`: a family of points of `ℝ³` that is
`δ`-separated and contained in the ball of radius `r` around the origin has at most
`(√3·(2r/δ) + 2)³` elements.

The proof is the elementary grid argument.  Put `s := δ / √3`.  Partition `ℝ³` into
half-open cubes of side `s`, indexed by `ℤ³` through the floored coordinates
`K i j = ⌊(x i) j / s⌋`.  Two distinct points falling in the same cube have all their
coordinate differences of modulus `< s`, hence their distance is `< s·√3 = δ`, which
contradicts `δ`-separation; so `i ↦ K i` is injective.  The range of `K` is contained in
a product of three copies of `Finset.Icc ⌊-R⌋ ⌊R⌋` where `R = r/s`, whose cardinality is
at most `2R + 2`; hence `#ι ≤ (2R+2)³ = (√3·(2r/δ) + 2)³`.
-/

namespace Work.BoseBogFS

/-- Two reals `a`, `b` whose quotients by `s > 0` have the same floor lie in the same
half-open cell of the grid of mesh `s`, hence `|a - b| < s`. -/
private lemma abs_sub_lt_of_floor_div_eq {s a b : ℝ} (hs : 0 < s)
    (h : ⌊a / s⌋ = ⌊b / s⌋) : |a - b| < s := by
  have h1 : (⌊a / s⌋ : ℝ) ≤ a / s := Int.floor_le _
  have h2 : a / s < (⌊a / s⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have h3 : (⌊b / s⌋ : ℝ) ≤ b / s := Int.floor_le _
  have h4 : b / s < (⌊b / s⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  rw [← h] at h3 h4
  have e1 : (⌊a / s⌋ : ℝ) * s ≤ a := (le_div_iff₀ hs).mp h1
  have e2 : a < ((⌊a / s⌋ : ℝ) + 1) * s := (div_lt_iff₀ hs).mp h2
  have e3 : (⌊a / s⌋ : ℝ) * s ≤ b := (le_div_iff₀ hs).mp h3
  have e4 : b < ((⌊a / s⌋ : ℝ) + 1) * s := (div_lt_iff₀ hs).mp h4
  rw [abs_lt]
  constructor <;> linarith

/-- If each coordinate of `v : ℝ³` has modulus `< s` then `‖v‖ < √3 · s`. -/
private lemma norm_lt_sqrt_three_mul {s : ℝ} (hs : 0 < s)
    (v : EuclideanSpace ℝ (Fin 3)) (hv : ∀ j, |v j| < s) :
    ‖v‖ < Real.sqrt 3 * s := by
  have hsq : ‖v‖ ^ 2 = ∑ j : Fin 3, (v j) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have hlt : ∀ j : Fin 3, (v j) ^ 2 < s ^ 2 := by
    intro j
    rw [sq_lt_sq, abs_of_nonneg hs.le]
    exact hv j
  have hsum : ∑ j : Fin 3, (v j) ^ 2 < ∑ _j : Fin 3, s ^ 2 :=
    Finset.sum_lt_sum_of_nonempty (by simp) (fun j _ => hlt j)
  rw [Finset.sum_const, Finset.card_univ] at hsum
  simp only [Fintype.card_fin, nsmul_eq_mul] at hsum
  have hkey : ‖v‖ ^ 2 < (Real.sqrt 3 * s) ^ 2 := by
    rw [hsq, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    exact hsum
  rw [sq_lt_sq] at hkey
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)] at hkey

/-- The integers in `[⌊-R⌋, ⌊R⌋]` are at most `2R + 2` in number, for `R ≥ 0`. -/
private lemma card_Icc_floor_le (R : ℝ) (hR : 0 ≤ R) :
    ((Finset.Icc ⌊-R⌋ ⌊R⌋ : Finset ℤ).card : ℝ) ≤ 2 * R + 2 := by
  rw [Int.card_Icc]
  set n : ℤ := ⌊R⌋ + 1 - ⌊-R⌋ with hn_def
  have hn_nonneg : 0 ≤ n := by
    have h1 : (0:ℤ) ≤ ⌊R⌋ := Int.le_floor.mpr (by simpa using hR)
    have h2 : ⌊-R⌋ ≤ 0 := by
      have := Int.floor_mono (show -R ≤ (0:ℝ) by linarith)
      simpa using this
    simp only [hn_def]; linarith
  have hncast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
    have hz : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn_nonneg
    exact_mod_cast hz
  rw [hncast]
  have hf : (⌊R⌋ : ℝ) ≤ R := Int.floor_le R
  have hf2 : -R - 1 < (⌊-R⌋ : ℝ) := by
    have := Int.lt_floor_add_one (-R); linarith
  simp only [hn_def]
  push_cast
  linarith

/-- A map `K : ι → (Fin 3 → ℤ)` that is injective and takes its values in a product of
three copies of `S` has card at most `#S ^ 3`. -/
private lemma card_le_pow_three {ι : Type*} [Fintype ι] (K : ι → Fin 3 → ℤ)
    (hinj : Function.Injective K) (S : Finset ℤ) (hmem : ∀ i j, K i j ∈ S) :
    (Finset.univ : Finset ι).card ≤ S.card ^ 3 := by
  have hmap : Set.MapsTo K (↑(Finset.univ : Finset ι))
      (↑(Fintype.piFinset (fun _ : Fin 3 => S))) := by
    intro i _
    exact Finset.mem_coe.mpr (Fintype.mem_piFinset.mpr (fun j => hmem i j))
  have hinjOn : Set.InjOn K (↑(Finset.univ : Finset ι)) := by
    rw [Finset.coe_univ]; exact hinj.injOn
  have hle := Finset.card_le_card_of_injOn K hmap hinjOn
  rw [Fintype.card_piFinset] at hle
  have h2 : (∏ _j : Fin 3, S.card) = S.card ^ 3 := by simp
  rw [h2] at hle
  exact hle

theorem card_le_of_separated {ι : Type*} [Fintype ι] (x : ι → EuclideanSpace ℝ (Fin 3))
    {δ r : ℝ} (hδ : 0 < δ) (hr0 : 0 ≤ r)
    (hsep : ∀ i j : ι, i ≠ j → δ ≤ ‖x i - x j‖) (hr : ∀ i : ι, ‖x i‖ ≤ r) :
    ((Finset.univ : Finset ι).card : ℝ) ≤ (Real.sqrt 3 * (2 * r / δ) + 2) ^ 3 := by
  set s : ℝ := δ / Real.sqrt 3 with hs
  have hs_pos : 0 < s := by rw [hs]; positivity
  have hsδ : Real.sqrt 3 * s = δ := by rw [hs]; field_simp
  set R : ℝ := r / s with hRdef
  have hR0 : 0 ≤ R := by rw [hRdef]; exact div_nonneg hr0 hs_pos.le
  set K : ι → Fin 3 → ℤ := fun i j => ⌊x i j / s⌋ with hK
  -- The floored cell index is injective, because two points in one cell are closer than `δ`.
  have hinj : Function.Injective K := by
    intro i i' hii
    by_contra hne
    have hd : δ ≤ ‖x i - x i'‖ := hsep i i' hne
    have hcoord : ∀ j : Fin 3, |x i j - x i' j| < s := fun j =>
      abs_sub_lt_of_floor_div_eq hs_pos (by
        have := congrFun hii j
        simpa [hK] using this)
    have hnorm : ‖x i - x i'‖ < Real.sqrt 3 * s :=
      norm_lt_sqrt_three_mul hs_pos (x i - x i') (fun j => by
        have := hcoord j
        simpa using this)
    rw [hsδ] at hnorm
    linarith
  -- Every cell index occuring lies in the box `[⌊-R⌋, ⌊R⌋]³`.
  have hmem : ∀ i (j : Fin 3), K i j ∈ (Finset.Icc ⌊-R⌋ ⌊R⌋ : Finset ℤ) := by
    intro i j
    have hxj : |x i j| ≤ r := by
      have h1 : |x i j| ≤ ‖x i‖ := by simpa using PiLp.norm_apply_le (x i) j
      exact le_trans h1 (hr i)
    obtain ⟨hlo, hhi⟩ := abs_le.mp hxj
    rw [Finset.mem_Icc]
    constructor
    · have hfl : ((K i j : ℤ) : ℝ) ≤ x i j / s := by
        rw [hK]; exact Int.floor_le _
      have hlt : x i j / s < ((K i j : ℤ) : ℝ) + 1 := by
        rw [hK]; exact Int.lt_floor_add_one _
      have h2 : x i j < (((K i j : ℤ) : ℝ) + 1) * s := (div_lt_iff₀ hs_pos).mp hlt
      have h3 : -r < (((K i j : ℤ) : ℝ) + 1) * s := lt_of_le_of_lt (by linarith) h2
      have h4 : -r / s < ((K i j : ℤ) : ℝ) + 1 := (div_lt_iff₀ hs_pos).mpr h3
      have hRneg : -r / s = -R := by rw [hRdef, neg_div]
      rw [hRneg] at h4
      have hfr : ((⌊-R⌋ : ℤ) : ℝ) ≤ -R := Int.floor_le (-R)
      have hcast : ((⌊-R⌋ : ℤ) : ℝ) < (((K i j) + 1 : ℤ) : ℝ) := by
        push_cast
        linarith
      have := Int.cast_lt.mp hcast
      omega
    · have hfl : ((K i j : ℤ) : ℝ) ≤ x i j / s := by
        rw [hK]; exact Int.floor_le _
      have h1 : ((K i j : ℤ) : ℝ) * s ≤ x i j := (le_div_iff₀ hs_pos).mp hfl
      have h2 : ((K i j : ℤ) : ℝ) * s ≤ r := le_trans h1 hhi
      have h3 : ((K i j : ℤ) : ℝ) ≤ r / s := (le_div_iff₀ hs_pos).mpr h2
      rw [← hRdef] at h3
      exact Int.le_floor.mpr h3
  have hcard : (Finset.univ : Finset ι).card ≤ (Finset.Icc ⌊-R⌋ ⌊R⌋ : Finset ℤ).card ^ 3 :=
    card_le_pow_three K hinj _ hmem
  have hS : (((Finset.Icc ⌊-R⌋ ⌊R⌋ : Finset ℤ).card : ℕ) : ℝ) ≤ 2 * R + 2 :=
    card_Icc_floor_le R hR0
  have h1 : ((Finset.univ : Finset ι).card : ℝ)
      ≤ (((Finset.Icc ⌊-R⌋ ⌊R⌋ : Finset ℤ).card : ℕ) : ℝ) ^ 3 := by
    exact_mod_cast hcard
  have h2 : (((Finset.Icc ⌊-R⌋ ⌊R⌋ : Finset ℤ).card : ℕ) : ℝ) ^ 3 ≤ (2 * R + 2) ^ 3 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hS 3
  have hmain : ((Finset.univ : Finset ι).card : ℝ) ≤ (2 * R + 2) ^ 3 := le_trans h1 h2
  have hReq : 2 * R + 2 = Real.sqrt 3 * (2 * r / δ) + 2 := by rw [hRdef, hs]; field_simp
  rwa [hReq] at hmain

end Work.BoseBogFS
