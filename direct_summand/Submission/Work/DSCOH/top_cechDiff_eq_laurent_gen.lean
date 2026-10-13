import Mathlib
import Submission.Work.DSCOH.ShiftToolkit

open MvPolynomial

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The general inequality `z ≤ (z.toNat : ℤ)`, valid for every integer `z`. -/
lemma int_le_toNat_self (z : ℤ) : z ≤ ((z.toNat : ℕ) : ℤ) := by
  rcases le_total z 0 with h | h
  · rw [Int.toNat_of_nonpos h]; exact h
  · rw [Int.toNat_of_nonneg h]

/-- The exponent vector of the numerator of the chart element of the chart `univ \ {i₀}` that
localizes to the Laurent monomial `xᵝ`: `β i₀` on `i₀`, and `β j + K` elsewhere. -/
noncomputable def gammaVec (β : Fin n → ℤ) (i₀ : Fin n) (K : ℕ) : Fin n → ℕ :=
  fun j => (β j + (if j = i₀ then 0 else (K:ℤ))).toNat

/-- The structure map `resAt` on the explicit fractions `m / X_S^k`: it multiplies the numerator
by `X_{T\S}^k`, the product of the variables inverted when passing from `S` to `T`. -/
private lemma resAt_divPow_toLoc (S T : Finset (Fin n)) (h : S ⊆ T) (k : ℕ) (m : Poly A n) :
    resAt (A := A) (M := Poly A n) h
      (divPow (A := A) (M := Poly A n) S k (toLoc (A := A) (M := Poly A n) S m)) =
      divPow (A := A) (M := Poly A n) T k
        (toLoc (A := A) (M := Poly A n) T (monomial (A := A) (T \ S) ^ k * m)) := by
  have hpoly : (monomial (A := A) T) ^ k =
      (monomial (A := A) S) ^ k * (monomial (A := A) (T \ S)) ^ k := by
    rw [show monomial (A := A) T = monomial (A := A) S * monomial (A := A) (T \ S) from by
      unfold monomial Var; rw [← Finset.prod_sdiff h]; exact mul_comm _ _]
    rw [mul_pow]
  rw [divPow_toLoc_eq_mk, resAt_mk, divPow_toLoc_eq_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, one_smul, den_coe, smul_eq_mul]
  rw [hpoly, mul_assoc]

/-- The sum of the exponent vector `gammaVec β i₀ K` is `K * (n-1) - d` when `∑ β = -d`. -/
lemma gamma_sum_aux {n d : ℕ} (hn : 1 ≤ n) {β : Fin n → ℤ} (hβ : ∑ i, β i = -(d:ℤ))
    (i₀ : Fin n) (hi₀ : 0 ≤ β i₀) :
    (∑ j, (β j + (if j = i₀ then 0 else ((∑ i, (-(β i)).toNat : ℕ):ℤ))).toNat)
      = (∑ i, (-(β i)).toNat) * (n-1) - d := by
  set K : ℕ := ∑ i, (-(β i)).toNat with hKdef
  have hK : ∀ i, -(β i) ≤ (K : ℤ) := fun i => le_sum_toNat β i
  have hγcast : ∀ j, (((β j + (if j = i₀ then 0 else (K:ℤ))).toNat : ℕ) : ℤ)
      = β j + (if j = i₀ then 0 else (K:ℤ)) := by
    intro j
    apply Int.toNat_of_nonneg
    by_cases hj : j = i₀
    · simp only [hj, ite_true, add_zero]; linarith
    · simp only [hj, ite_false]
      have := hK j; linarith
  have key : ((∑ j, (β j + (if j = i₀ then 0 else (K:ℤ))).toNat : ℕ) : ℤ)
      = (K:ℤ) * ((n:ℤ) - 1) - d := by
    rw [Nat.cast_sum]
    simp only [hγcast]
    rw [Finset.sum_add_distrib, hβ]
    have h1 : (∑ j : Fin n, (if j = i₀ then (0:ℤ) else (K:ℤ))) = (n:ℤ) * (K:ℤ) - (K:ℤ) := by
      have hc : ∀ j : Fin n, (if j = i₀ then (0:ℤ) else (K:ℤ))
          = (K:ℤ) - (if j = i₀ then (K:ℤ) else 0) := by
        intro j; by_cases hj : j = i₀ <;> simp [hj]
      simp only [hc]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Finset.sum_ite_eq']
      simp
    rw [h1]; ring
  have hcast : ((K * (n-1) : ℕ) : ℤ) = (K:ℤ) * ((n:ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hn]; push_cast; ring
  have hle : d ≤ K * (n-1) := by
    have h0 : (0:ℤ) ≤ (K:ℤ) * ((n:ℤ) - 1) - d := by rw [← key]; exact Int.natCast_nonneg _
    rw [← hcast] at h0
    have : (d:ℤ) ≤ ((K * (n-1) : ℕ) : ℤ) := by linarith
    exact_mod_cast this
  rw [show (∑ j, (β j + (if j = i₀ then 0 else (K:ℤ))).toNat) = ((K:ℤ)*((n:ℤ)-1) - d).toNat from by
        rw [← key, Int.toNat_natCast]]
  rw [← hcast, ← Nat.cast_sub hle, Int.toNat_natCast]

/-- The `T`-component of the Čech differential, spelled out on the underlying elements of the
degree-zero parts of the chart localizations. -/
lemma cechDiff_apply_val (M : Type*) [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M] (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ]
    (q : ℕ) (x : CechTerm (A := A) (n := n) (M := M) ℳ q)
    (T : {S : Finset (Fin n) // S.card = q + 1 + 1}) :
    ((cechDiff (A := A) (n := n) (M := M) ℳ q x) T : locAt (A := A) (M := M) T.1) =
      ∑ i ∈ T.1.attach, ((-1 : ℤ) ^ ((T.1.filter fun j => j < i.1)).card) •
        resAt (M := M) (Finset.erase_subset i.1 T.1)
          (x ⟨T.1.erase i.1, by rw [Finset.card_erase_of_mem i.2]; omega⟩ :
            locAt (A := A) (M := M) (T.1.erase i.1)) := by
  simp only [cechDiff, LinearMap.pi_apply, cechDiffComp, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Submodule.subtype_apply, map_zsmul, Submodule.subtype_apply]
  rfl

theorem top_cechDiff_eq_laurent_gen {A : Type*} [CommRing A] {n : ℕ} (d : ℕ)
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)] (hn : 2 ≤ n) {q : ℕ}
    {β : Fin n → ℤ}
    (hβ : (∑ i, β i) = -(d : ℤ)) (hpos : ∃ i, 0 ≤ β i)
    (h : (Finset.univ : Finset (Fin n)).card = q + 1 + 1) :
    ∃ x : CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) q,
      (cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) q) x
        ⟨Finset.univ, h⟩
        = ⟨laurent (A := A) (n := n) β, laurent_mem_degZero (A := A) (n := n) hβ⟩ := by
  classical
  obtain ⟨i₀, hi₀⟩ := hpos
  have huniv : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hn1 : 1 ≤ n := by omega
  have hS₀card : (Finset.univ.erase i₀ : Finset (Fin n)).card = q + 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), huniv]; omega
  set K : ℕ := ∑ i, (-(β i)).toNat with hKdef
  have hγsum : ∑ j, gammaVec β i₀ K j = K * (n - 1) - d := by
    simp only [gammaVec, hKdef]
    exact gamma_sum_aux hn1 hβ i₀ hi₀
  have hSc : (Finset.univ.erase i₀ : Finset (Fin n)).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), huniv]
  have hmem : xpow (A := A) (n := n) (gammaVec β i₀ K) ∈
      shift (A := A) (n := n) d (K * (Finset.univ.erase i₀).card) := by
    rw [hSc]
    have hdK : d ≤ K := by
      have h1 : (d:ℤ) = ∑ j, (-(β j)) := by rw [Finset.sum_neg_distrib, hβ]; ring
      have h3 : ((K : ℕ) : ℤ) = ∑ j, (((-(β j)).toNat : ℕ) : ℤ) := by
        rw [hKdef, Nat.cast_sum]
      have h2 : (∑ j, (-(β j))) ≤ ∑ j, (((-(β j)).toNat : ℕ) : ℤ) :=
        Finset.sum_le_sum (fun j _ => int_le_toNat_self (-(β j)))
      have : (d:ℤ) ≤ (K:ℤ) := by rw [h1, h3]; exact h2
      exact_mod_cast this
    have hle : d ≤ K * (n - 1) := by
      have : 1 ≤ n - 1 := by omega
      calc d ≤ K := hdK
        _ = K * 1 := (mul_one K).symm
        _ ≤ K * (n - 1) := Nat.mul_le_mul_left K this
    rw [shift_of_le hle, ← hγsum]
    exact xpow_mem_homSub (A := A) (n := n) _
  set w : locAt (A := A) (M := Poly A n) (Finset.univ.erase i₀) :=
    divPow (A := A) (M := Poly A n) (Finset.univ.erase i₀) K
      (toLoc (A := A) (M := Poly A n) (Finset.univ.erase i₀) (xpow (A := A) (n := n) (gammaVec β i₀ K))) with hwdef
  have hwmem : w ∈ degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) (Finset.univ.erase i₀) := by
    rw [hwdef]
    exact divPow_toLoc_mem (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d)
      (Finset.univ.erase i₀) K hmem
  have hres : resAt (A := A) (M := Poly A n) (Finset.erase_subset i₀ (Finset.univ : Finset (Fin n))) w
      = laurent (A := A) (n := n) β := by
    rw [hwdef, resAt_divPow_toLoc]
    have hset : Finset.univ \ Finset.univ.erase i₀ = ({i₀} : Finset (Fin n)) := by
      rw [Finset.sdiff_erase (Finset.mem_univ i₀), Finset.sdiff_self]; simp
    have hmono : monomial (A := A) ({i₀} : Finset (Fin n)) = (MvPolynomial.X i₀ : Poly A n) := by
      simp [monomial, Var]
    have hxpow : xpow (A := A) (n := n) (fun j => if j = i₀ then K else 0) = (MvPolynomial.X i₀ : Poly A n) ^ K := by
      rw [xpow]; rw [Finset.prod_eq_single i₀]
      · simp
      · intro j _ hj; rw [ite_eq_right hj, pow_zero]
      · intro hi; exact absurd (Finset.mem_univ i₀) hi
    have hγfunpt : ∀ j : Fin n, (if j = i₀ then K else 0) + gammaVec β i₀ K j = (β j + (K:ℤ)).toNat := by
      intro j
      by_cases hj : j = i₀
      · rw [hj]; simp only [gammaVec, ite_true, add_zero]
        rw [Int.toNat_add hi₀ (Int.natCast_nonneg K), Int.toNat_natCast, Nat.add_comm]
      · simp only [gammaVec, hj, ite_false, zero_add]
    rw [hset, hmono, ← hxpow, ← xpow_add,
      show ((fun j : Fin n => if j = i₀ then K else 0) + gammaVec β i₀ K)
          = (fun j : Fin n => (β j + (K:ℤ)).toNat) from funext hγfunpt]
    rw [show laurent (A := A) (n := n) β = laurentAt (A := A) (n := n) β K from by
      unfold laurent; rw [hKdef]]
    rfl
  set ε : ℤ := (-1 : ℤ) ^ (Finset.univ.filter (fun j => j < i₀)).card with hεdef
  refine ⟨(fun (S : {S : Finset (Fin n) // S.card = q + 1}) =>
    if hh : S.1 = Finset.univ.erase i₀ then hh.symm ▸ (ε • (⟨w, hwmem⟩ : degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) (Finset.univ.erase i₀))) else 0), ?_⟩
  apply Subtype.ext
  rw [cechDiff_apply_val]
  refine (Finset.sum_eq_single (⟨i₀, Finset.mem_univ i₀⟩ : {x // x ∈ (Finset.univ : Finset (Fin n))}) ?_ ?_).trans ?_
  · intro b hb hbne
    have hbne' : b.1 ≠ i₀ := fun hh => hbne (Subtype.ext hh)
    have hne : ¬ (Finset.univ.erase b.1 = Finset.univ.erase i₀) :=
      fun heq => hbne' ((Finset.erase_inj Finset.univ (Finset.mem_univ b.1)).mp heq)
    simp only [dite_eq_right hne]
    simp
  · intro hmem2
    exact absurd (Finset.mem_attach _ _) hmem2
  · simp only [dite_true]
    have hcoe : (↑(ε • (⟨w, hwmem⟩ : degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) (Finset.univ.erase i₀))) : locAt (A := A) (M := Poly A n) (Finset.univ.erase i₀)) = ε • w := by
      rw [← Submodule.subtype_apply, map_zsmul, Submodule.subtype_apply]
    rw [hcoe, map_zsmul, hres, ← hεdef, smul_smul]
    have hεsq : ε * ε = 1 := by
      rw [hεdef, ← mul_pow, show ((-1:ℤ) * (-1)) = 1 from by norm_num, one_pow]
    rw [hεsq, one_smul]

end Work.DSCOH
