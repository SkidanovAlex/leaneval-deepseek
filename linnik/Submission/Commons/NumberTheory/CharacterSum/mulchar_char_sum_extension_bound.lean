import Mathlib
import Submission.Commons.NumberTheory.Stepanov.superelliptic_char_sum_bound
import Submission.Commons.FieldTheory.FiniteField.pow_card_sub_one_div_eq_one_iff
import Submission.Commons.NumberTheory.CharacterSum.superelliptic_point_card
import Submission.Commons.FieldTheory.FiniteField.not_const_mul_pow_map

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false



namespace Commons.NumberTheory.CharacterSum

open Polynomial
open scoped BigOperators

section Basic

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

lemma not_isUnit_zero_field (K : Type*) [Field K] : ¬ IsUnit (0 : K) :=
  fun h => by obtain ⟨u, hu⟩ := h; exact u.ne_zero hu

/-- The multiplicative character of `E` obtained by composing `χ : MulChar F ℂ` with the
norm `N_{E/F} : E → F`. -/
noncomputable def normCompMulChar [Module.Finite F E] [Module.Free F E] (χ : MulChar F ℂ) :
    MulChar E ℂ :=
  MulChar.ofUnitHom (χ.toUnitHom.comp (Units.map (Algebra.norm F)))

lemma normCompMulChar_apply [Module.Finite F E] [Module.Free F E] (χ : MulChar F ℂ) (x : E) :
    normCompMulChar (F := F) χ x = χ (Algebra.norm F x) := by
  by_cases hx : x = 0
  · subst hx
    rw [normCompMulChar, Algebra.norm_zero, MulChar.map_nonunit _ (not_isUnit_zero_field E),
      MulChar.map_nonunit χ (not_isUnit_zero_field F)]
  · have hxu : ((Units.mk0 x hx : Eˣ) : E) = x := Units.val_mk0 hx
    rw [← hxu, normCompMulChar, MulChar.ofUnitHom_eq, MulChar.equivToUnitHom_symm_coe]
    rw [MonoidHom.comp_apply, MulChar.toUnitHom_eq, MulChar.coe_equivToUnitHom, Units.coe_map]

end Basic

section NormPow

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]
  [Module.Finite F E] [Module.Free F E]

/-- The norm of an element of a finite field extension, as a power of the element
(inside the extension). -/
lemma algebraMap_norm_eq_pow_sum_range (n : ℕ) (hn : Module.finrank F E = n) (x : E) :
    algebraMap F E (Algebra.norm F x) = x ^ (∑ i ∈ Finset.range n, Fintype.card F ^ i) := by
  rw [FiniteField.algebraMap_norm_eq_prod_pow F E x, hn, Nat.card_eq_fintype_card,
    Finset.prod_pow_eq_pow_sum]

lemma card_eq_pow_finrank' (n : ℕ) (hn : Module.finrank F E = n) :
    Fintype.card E = Fintype.card F ^ n := by
  rw [Module.card_eq_pow_finrank (K := F) (V := E), hn]

/-- The key exponent identity `((q^n-1)/(q-1)) * ((q-1)/e) = (q^n-1)/e`. -/
lemma geomSum_mul_div (q n e : ℕ) (hq : 2 ≤ q) (he : e ∣ q - 1) (he0 : e ≠ 0) :
    (∑ i ∈ Finset.range n, q ^ i) * ((q - 1) / e) = (q ^ n - 1) / e := by
  have hdiv : (q - 1) ∣ q ^ n - 1 := by
    have h2 : (1 : ℕ) ≡ q [MOD q - 1] :=
      (Nat.modEq_iff_dvd' (by omega : 1 ≤ q)).mpr dvd_rfl
    have h3 : (1 : ℕ) ≡ q ^ n [MOD q - 1] := by simpa using h2.pow n
    exact (Nat.modEq_iff_dvd'
      (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero n (by omega : q ≠ 0)))).mp h3
  have hA : (∑ i ∈ Finset.range n, q ^ i) = (q ^ n - 1) / (q - 1) := Nat.geomSum_eq hq n
  have hqe : (q - 1) / e * e = q - 1 := Nat.div_mul_cancel he
  have hqA : (q ^ n - 1) / (q - 1) * (q - 1) = q ^ n - 1 := Nat.div_mul_cancel hdiv
  have key : (∑ i ∈ Finset.range n, q ^ i) * ((q - 1) / e) * e = q ^ n - 1 := by
    rw [mul_assoc, hqe, hA, hqA]
  rw [← key, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero he0)]

/-- **Norm-power identity** (inside the extension): for `u` in a finite field extension `E/F`
and `e ∣ #F - 1`, the image of `(N u) ^ ((#F-1)/e)` in `E` is `u ^ ((#E-1)/e)`. -/
lemma algebraMap_norm_pow_eq_pow (e n : ℕ) (hn : Module.finrank F E = n)
    (hdiv : e ∣ Fintype.card F - 1) (he0 : e ≠ 0) (u : E) :
    algebraMap F E ((Algebra.norm F u) ^ ((Fintype.card F - 1) / e)) =
      u ^ ((Fintype.card E - 1) / e) := by
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  rw [map_pow, algebraMap_norm_eq_pow_sum_range n hn u, ← pow_mul,
    geomSum_mul_div (Fintype.card F) n e hq hdiv he0, card_eq_pow_finrank' n hn]

end NormPow


section Kernel

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]
  [Module.Finite F E] [Module.Free F E]

/-- `e` divides `#E - 1` when `e` divides `#F - 1` and `#E = #F ^ n`. -/
lemma dvd_card_sub_one_of_dvd_card_sub_one (e n : ℕ) (hn : Module.finrank F E = n)
    (hdiv : e ∣ Fintype.card F - 1) : e ∣ Fintype.card E - 1 := by
  rw [card_eq_pow_finrank' n hn]
  have h2 : (1 : ℕ) ≡ Fintype.card F [MOD e] :=
    (Nat.modEq_iff_dvd' (Fintype.card_pos)).mpr hdiv
  have h3 : (1 : ℕ) ≡ Fintype.card F ^ n [MOD e] := by simpa using h2.pow n
  exact (Nat.modEq_iff_dvd'
    (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero n Fintype.card_ne_zero))).mp h3

/-- **Kernel identity**: the kernel of `χ ∘ N_{E/F}` on `Eˣ` is exactly the subgroup of
`e`-th powers. -/
lemma normCompMulChar_eq_one_iff (e n : ℕ) (he : 0 < e) (hn : Module.finrank F E = n)
    (hdiv : e ∣ Fintype.card F - 1) (χ : MulChar F ℂ) (hord : orderOf χ = e) (u : Eˣ) :
    normCompMulChar (F := F) χ (u : E) = 1 ↔ u ∈ (powMonoidHom e).range := by
  have hNu : Algebra.norm F (u : E) ≠ 0 :=
    fun h => u.ne_zero ((Algebra.norm_eq_zero_iff).mp h)
  have hE : Fintype.card E = Fintype.card F ^ n := card_eq_pow_finrank' n hn
  have hdivE : e ∣ Fintype.card E - 1 := dvd_card_sub_one_of_dvd_card_sub_one e n hn hdiv
  rw [normCompMulChar_apply]
  have h1 : χ (Algebra.norm F (u : E)) = 1 ↔
      Units.mk0 (Algebra.norm F (u : E)) hNu ∈ (powMonoidHom e).range := by
    have h := Commons.NumberTheory.CharacterSum.mem_range_powMonoidHom_iff_apply_eq_one
      (F := F) e he hdiv χ hord (Units.mk0 (Algebra.norm F (u : E)) hNu)
    rw [Units.val_mk0] at h
    exact h.symm
  have h2 : Units.mk0 (Algebra.norm F (u : E)) hNu ∈ (powMonoidHom e).range ↔
      (Units.mk0 (Algebra.norm F (u : E)) hNu : Fˣ) ^ ((Fintype.card F - 1) / e) = 1 :=
    (Commons.FieldTheory.FiniteField.pow_card_sub_one_div_eq_one_iff (K := F) e hdiv _).symm
  have h3 : (Units.mk0 (Algebra.norm F (u : E)) hNu : Fˣ) ^ ((Fintype.card F - 1) / e) = 1 ↔
      (u : E) ^ ((Fintype.card E - 1) / e) = 1 := by
    have hA : (Algebra.norm F (u : E)) ^ ((Fintype.card F - 1) / e) = 1 ↔
        algebraMap F E ((Algebra.norm F (u : E)) ^ ((Fintype.card F - 1) / e)) = 1 :=
      (map_eq_one_iff (algebraMap F E) (algebraMap F E).injective).symm
    have hB : algebraMap F E ((Algebra.norm F (u : E)) ^ ((Fintype.card F - 1) / e)) = 1 ↔
        (u : E) ^ ((Fintype.card E - 1) / e) = 1 := by
      rw [algebraMap_norm_pow_eq_pow e n hn hdiv he.ne' (u : E)]
    rw [Units.ext_iff, Units.val_one, Units.val_pow_eq_pow_val, Units.val_mk0]
    exact hA.trans hB
  have h4 : (u : E) ^ ((Fintype.card E - 1) / e) = 1 ↔ u ∈ (powMonoidHom e).range := by
    rw [← Units.val_pow_eq_pow_val, Units.val_eq_one]
    exact Commons.FieldTheory.FiniteField.pow_card_sub_one_div_eq_one_iff (K := E) e hdivE u
  exact h1.trans (h2.trans (h3.trans h4))

/-- `√(x ^ n) = (√x) ^ n` for `x ≥ 0`. -/
lemma sqrt_pow_eq (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_natCast x n,
    ← Real.rpow_natCast (x ^ (1 / 2 : ℝ)) n,
    ← Real.rpow_mul hx n (1 / 2 : ℝ), ← Real.rpow_mul hx (1 / 2 : ℝ) (n : ℝ), mul_comm]

/-- The pointwise Fourier identity: if `ζ` is a primitive `e`-th root of unity in `ℂ` and
`z = 0` or `z ^ e = 1`, then `∑_j [z = ζ ^ j] ζ ^ j = z`. -/
lemma sum_ite_eq_pow_of_isPrimitiveRoot {ζ : ℂ} {e : ℕ} (he0 : e ≠ 0) (hζ : IsPrimitiveRoot ζ e)
    {z : ℂ} (hz : z = 0 ∨ z ^ e = 1) :
    ∑ j : Fin e, (if z = ζ ^ (j : ℕ) then ζ ^ (j : ℕ) else 0) = z := by
  haveI : NeZero e := ⟨he0⟩
  rcases hz with rfl | hz
  · refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [if_neg]
    exact fun h => pow_ne_zero _ (hζ.ne_zero (NeZero.ne e)) h.symm
  · obtain ⟨i, hi, hzi⟩ := hζ.eq_pow_of_pow_eq_one hz
    rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin e)]
    · rw [if_pos hzi.symm]
      exact hzi
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Fin.ext (hζ.pow_inj b.isLt hi (h.symm.trans hzi.symm)))
    · intro h
      exact absurd (Finset.mem_univ _) h

end Kernel

section Main

/-- For a finite field `K` and `y ≠ 0`, a multiplicative character does not vanish at `y`. -/
lemma mulChar_apply_ne_zero {K : Type*} [Field K] (χ : MulChar K ℂ) {y : K} (hy : y ≠ 0) :
    χ y ≠ 0 := by
  have h := MulChar.coe_toUnitHom χ (Units.mk0 y hy)
  rw [Units.val_mk0] at h
  rw [← h]
  exact (χ.toUnitHom (Units.mk0 y hy)).ne_zero

/-- The number of elements of a set defined by a decidable predicate on a finite type
equals the cardinality of the corresponding filtered finset. -/
lemma ncard_setOf_eq_card_filter {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (({x : α | p x} : Set α).ncard) = (Finset.univ.filter p).card := by
  rw [Set.ncard_eq_toFinset_card]
  congr 1
  ext x
  simp

lemma norm_ofReal_eq_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h1 : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  have h2 : |r| ^ 2 = r ^ 2 := sq_abs r
  nlinarith only [norm_nonneg ((r : ℝ) : ℂ), abs_nonneg r, h1, h2]

theorem mulchar_char_sum_extension_bound (e d : ℕ) (he : 2 ≤ e) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {F : Type*} [Field F] [Fintype F] [DecidableEq F], e ∣ Fintype.card F - 1 →
      ∀ (χ : MulChar F ℂ), χ ≠ 1 → orderOf χ = e →
      ∀ (f : Polynomial F), f.natDegree ≤ d →
      (∀ p : ℕ, p.Prime → p ∣ e → ∀ (a : F) (h : Polynomial F),
        f ≠ Polynomial.C a * h ^ p) →
      ∀ (n : ℕ), 1 ≤ n →
      ∀ (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra F E]
        [Module.Finite F E] [Module.Free F E],
        Module.finrank F E = n →
        ‖∑ a : E, χ (Algebra.norm F ((f.map (algebraMap F E)).eval a))‖
          ≤ C * (Real.sqrt (Fintype.card F)) ^ n := by
  classical
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.NumberTheory.Stepanov.superelliptic_char_sum_bound e d he hd
  have hCpos : 0 < (e : ℝ) * (d : ℝ) + (e : ℝ) * ((e : ℝ) - 1) * C₀ := by
    have heR : (2 : ℝ) ≤ e := by exact_mod_cast he
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have h1 : (0 : ℝ) < (e : ℝ) := by linarith only [heR]
    have h2 : (0 : ℝ) < (e : ℝ) - 1 := by linarith only [heR]
    have h3 : (0 : ℝ) < (d : ℝ) := by linarith only [hdR]
    positivity
  refine ⟨(e : ℝ) * (d : ℝ) + (e : ℝ) * ((e : ℝ) - 1) * C₀, hCpos, ?_⟩
  intro F _ _ _ hdiv χ hχ hord f hfdeg hfnd n hn E _ _ _ _ _ _ hfin
  set q : ℕ := Fintype.card F with hq
  set N : ℕ := Fintype.card E with hN
  have he0 : e ≠ 0 := by omega
  have hq2 : 2 ≤ q := by rw [hq]; exact Fintype.one_lt_card
  have hN2 : 2 ≤ N := by rw [hN]; exact Fintype.one_lt_card
  have hcardN : N = q ^ n := by rw [hN, hq]; exact card_eq_pow_finrank' n hfin
  have hdivE : e ∣ N - 1 := by
    rw [hN]; exact dvd_card_sub_one_of_dvd_card_sub_one e n hfin hdiv
  have hsqrtN : Real.sqrt (N : ℝ) = (Real.sqrt (q : ℝ)) ^ n := by
    rw [hcardN, Nat.cast_pow]
    exact sqrt_pow_eq (q : ℝ) (by positivity) n
  by_cases hf0 : f = 0
  · subst hf0
    have hz : (∑ a : E, χ (Algebra.norm F ((Polynomial.map (algebraMap F E) 0).eval a))) = 0 := by
      simp only [Polynomial.map_zero, Polynomial.eval_zero, Algebra.norm_zero]
      rw [Finset.sum_eq_zero]
      intro a _
      exact MulChar.map_nonunit χ (not_isUnit_zero_field F)
    rw [hz, norm_zero]
    positivity
  set fE : Polynomial E := f.map (algebraMap F E) with hfE
  have hfE0 : fE ≠ 0 := by
    rw [hfE]
    exact fun h => hf0 ((Polynomial.map_eq_zero_iff (algebraMap F E).injective).mp h)
  set ψ : MulChar E ℂ := normCompMulChar (F := F) χ with hψdef
  have hψapply : ∀ x : E, ψ x = χ (Algebra.norm F x) := fun x => normCompMulChar_apply χ x
  have hψker : ∀ u : Eˣ, ψ (u : E) = 1 ↔ u ∈ (powMonoidHom e : Eˣ →* Eˣ).range :=
    fun u => normCompMulChar_eq_one_iff e n (by omega) hfin hdiv χ hord u
  have hψzero : ∀ x : E, ψ x = 0 ↔ x = 0 := by
    intro x
    rw [hψapply]
    constructor
    · intro h
      by_contra hx
      exact mulChar_apply_ne_zero χ (fun hh => hx ((Algebra.norm_eq_zero_iff).mp hh)) h
    · intro h
      rw [h, Algebra.norm_zero]
      exact MulChar.map_nonunit χ (not_isUnit_zero_field F)
  haveI : NeZero e := ⟨he0⟩
  -- the generator of `Eˣ` and the root of unity `γ = ψ g`
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Eˣ)
  have hordg : orderOf g = N - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units, hN]
  set γ : ℂ := ψ (g : E) with hγdef
  have hγne : γ ≠ 0 := by rw [hγdef]; exact mulChar_apply_ne_zero ψ (Units.ne_zero g)
  have hγe : γ ^ e = 1 := by
    have h1 : ψ ((g ^ e : Eˣ) : E) = 1 :=
      (hψker (g ^ e)).mpr ⟨g, by rw [powMonoidHom_apply]⟩
    rw [Units.val_pow_eq_pow_val, map_pow] at h1
    rw [hγdef]
    exact h1
  have hdvd1 : orderOf γ ∣ e := orderOf_dvd_iff_pow_eq_one.mpr hγe
  have hdvd2 : e ∣ orderOf γ := by
    set dd : ℕ := orderOf γ with hdd
    have hγdd : γ ^ dd = 1 := by rw [hdd]; exact pow_orderOf_eq_one γ
    have h1 : ψ ((g ^ dd : Eˣ) : E) = 1 := by
      rw [Units.val_pow_eq_pow_val, map_pow, ← hγdef, hγdd]
    have hmem : (g ^ dd) ∈ (powMonoidHom e : Eˣ →* Eˣ).range := (hψker (g ^ dd)).mp h1
    obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hmem
    have hcardunits : Fintype.card Eˣ = N - 1 := by rw [Fintype.card_units, hN]
    have hv1 : v ^ (N - 1) = 1 := by rw [← hcardunits]; exact pow_card_eq_one
    have hM : N - 1 = e * ((N - 1) / e) := (Nat.mul_div_cancel' hdivE).symm
    have hv' : v ^ (N - 1) = g ^ (dd * ((N - 1) / e)) := by
      have hfirst : v ^ (N - 1) = (v ^ e) ^ ((N - 1) / e) := by rw [← pow_mul, ← hM]
      rw [hfirst, ← powMonoidHom_apply e v, hv, ← pow_mul]
    have h4 : orderOf g ∣ dd * ((N - 1) / e) := by
      rw [orderOf_dvd_iff_pow_eq_one, ← hv', hv1]
    have h4' : (N - 1) ∣ dd * ((N - 1) / e) := by rwa [hordg] at h4
    have h4'' : e * ((N - 1) / e) ∣ dd * ((N - 1) / e) := by rwa [← hM]
    have hmpos : 0 < (N - 1) / e := by
      refine Nat.div_pos ?_ (Nat.pos_of_ne_zero he0)
      exact Nat.le_of_dvd (by omega) hdivE
    exact (Nat.mul_dvd_mul_iff_right hmpos).mp h4''
  have hordγ : orderOf γ = e := Nat.dvd_antisymm hdvd1 hdvd2
  have hγprim : IsPrimitiveRoot γ e := by
    rw [IsPrimitiveRoot.iff_def]
    refine ⟨hγe, fun l hl => ?_⟩
    rw [← hordγ]
    exact orderOf_dvd_iff_pow_eq_one.mpr hl
  -- values of `ψ ∘ fE` are `0` or `e`-th roots of unity
  have hval : ∀ a : E, ψ (fE.eval a) = 0 ∨ (ψ (fE.eval a)) ^ e = 1 := by
    intro a
    by_cases h : fE.eval a = 0
    · refine Or.inl ?_
      rw [h]
      exact (hψzero 0).mpr rfl  -- hmm
    · refine Or.inr ?_
      have hy : Algebra.norm F (fE.eval a) ≠ 0 := fun hh => h ((Algebra.norm_eq_zero_iff).mp hh)
      rw [hψapply]
      obtain ⟨ζ, hζmem, hζeq⟩ := MulChar.apply_mem_rootsOfUnity_orderOf χ hy
      rw [hord, mem_rootsOfUnity] at hζmem
      have hζ1 : (ζ : ℂ) ^ e = 1 := by
        rw [← Units.val_pow_eq_pow_val, hζmem, Units.val_one]
      rw [← hζeq, hζ1]
  -- the fibres of `ψ ∘ fE`
  set T : Fin e → ℕ := fun j =>
    (Finset.univ.filter (fun a : E => ψ (fE.eval a) = γ ^ (j : ℕ))).card with hTdef
  have hdecomp : (∑ a : E, ψ (fE.eval a))
      = ∑ j : Fin e, γ ^ (j : ℕ) * (T j : ℂ) := by
    have hpoint : ∀ a : E, ψ (fE.eval a) =
        ∑ j : Fin e, (if ψ (fE.eval a) = γ ^ (j : ℕ) then γ ^ (j : ℕ) else 0) :=
      fun a => (sum_ite_eq_pow_of_isPrimitiveRoot he0 hγprim (hval a)).symm
    rw [Finset.sum_congr rfl (fun a _ => hpoint a)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hkpos : 0 < (N - 1) / e := by
    refine Nat.div_pos ?_ (Nat.pos_of_ne_zero he0)
    exact Nat.le_of_dvd (by omega) hdivE
  -- kernel identity in power form
  have hψpow : ∀ x : E, ψ x = 1 ↔ x ^ ((N - 1) / e) = 1 := by
    intro x
    by_cases hx : x = 0
    · rw [hx]
      have h1 : ψ (0 : E) ≠ 1 := by
        rw [(hψzero 0).mpr rfl]
        exact zero_ne_one
      have h2 : (0 : E) ^ ((N - 1) / e) ≠ 1 := by
        rw [zero_pow (ne_of_gt hkpos)]
        exact zero_ne_one
      exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
    · have h3 : (Units.mk0 x hx : Eˣ) ^ ((Fintype.card E - 1) / e) = 1 ↔
          (x : E) ^ ((N - 1) / e) = 1 := by
        rw [← Units.val_eq_one, Units.val_pow_eq_pow_val, Units.val_mk0, ← hN]
      have h4 : ψ (x : E) = 1 ↔
          (Units.mk0 x hx : Eˣ) ^ ((Fintype.card E - 1) / e) = 1 := by
        have h5 := (hψker (Units.mk0 x hx)).trans
          ((Commons.FieldTheory.FiniteField.pow_card_sub_one_div_eq_one_iff (K := E) e hdivE
            (Units.mk0 x hx))).symm
        rwa [Units.val_mk0] at h5
      exact h4.trans h3
  -- the algebraic step: `ψ x = γ j ↔ ψ (x * u⁻¹) = 1`
  have hmul_inv : ∀ (x : E) (j : Fin e), ψ x = γ ^ (j : ℕ) ↔
      ψ (x * (((g ^ (j : ℕ) : Eˣ) : E))⁻¹) = 1 := by
    intro x j
    set u : E := ((g ^ (j : ℕ) : Eˣ) : E) with hu
    have hu0 : u ≠ 0 := by rw [hu]; exact Units.ne_zero _
    have hψu : ψ u = γ ^ (j : ℕ) := by
      rw [hu, Units.val_pow_eq_pow_val, map_pow, hγdef]
    have hcc : ψ (u⁻¹) * ψ u = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hu0, MulChar.map_one]
    have hccγ : ψ (u⁻¹) * γ ^ (j : ℕ) = 1 := by rw [← hψu]; exact hcc
    have h5 : ψ (u⁻¹) = (γ ^ (j : ℕ))⁻¹ := eq_inv_of_mul_eq_one_left hccγ
    constructor
    · intro hx
      rw [map_mul, hx, h5, mul_inv_cancel₀ (pow_ne_zero _ hγne)]
    · intro hx
      have h6 : ψ x * (γ ^ (j : ℕ))⁻¹ = 1 := by
        rw [← h5, ← map_mul, hx]
      have h7 : ψ x * (γ ^ (j : ℕ))⁻¹ * γ ^ (j : ℕ) = 1 * γ ^ (j : ℕ) := by rw [h6]
      rwa [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hγne), mul_one, one_mul] at h7
  -- each fibre is a Stepanov level set
  have hT_upper : ∀ j : Fin e, (T j : ℝ) ≤ (N : ℝ) / e + C₀ * Real.sqrt (N : ℝ) := by
    intro j
    set u : E := ((g ^ (j : ℕ) : Eˣ) : E) with hu
    set c : E := u⁻¹ with hc
    set g' : Polynomial E := Polynomial.C c * fE with hg'
    have hcne : c ≠ 0 := by rw [hc]; exact inv_ne_zero (by rw [hu]; exact Units.ne_zero _)
    have hset : ({a : E | ψ (fE.eval a) = γ ^ (j : ℕ)} : Set E)
        = {a : E | g'.eval a ^ ((N - 1) / e) = 1} := by
      ext a
      simp only [Set.mem_ofPred_eq, hg', Polynomial.eval_mul, Polynomial.eval_C]
      rw [mul_comm c (fE.eval a), hc]
      rw [hmul_inv (fE.eval a) j, hψpow (fE.eval a * u⁻¹)]
    have hg'deg : g'.natDegree ≤ d := by
      rw [hg']
      calc (Polynomial.C c * fE).natDegree
          ≤ (Polynomial.C c).natDegree + fE.natDegree := Polynomial.natDegree_mul_le
        _ = fE.natDegree := by rw [Polynomial.natDegree_C, zero_add]
        _ ≤ f.natDegree := by rw [hfE]; exact Polynomial.natDegree_map_le
        _ ≤ d := hfdeg
    have hg'nd : ∀ p : ℕ, p.Prime → p ∣ e → ∀ (a : E) (h : Polynomial E),
        g' ≠ Polynomial.C a * h ^ p := by
      intro p hp hpe a h hcon
      have hchar : (p : E) ≠ 0 := by
        intro hp0
        obtain ⟨m, hprime, hm⟩ := FiniteField.card E (ringChar E)
        have h1 : ringChar E ∣ p := (CharP.cast_eq_zero_iff E (ringChar E) p).mp hp0
        have h2 : p = ringChar E := (Nat.Prime.dvd_iff_eq hp hprime.ne_one).mp h1
        have hEN : Fintype.card E = p ^ (m : ℕ) := by rw [hm, h2]
        have hpN : p ∣ N := by
          rw [hN, hEN]
          exact dvd_pow_self p m.pos.ne'
        rw [hcardN] at hpN
        have hpq : p ∣ q := hp.dvd_of_dvd_pow hpN
        have hpq1 : p ∣ q - 1 := hpe.trans (hq ▸ hdiv)
        have h1dvd : p ∣ 1 := by
          have h := Nat.dvd_sub hpq hpq1
          rwa [show q - (q - 1) = 1 by omega] at h
        exact hp.not_dvd_one h1dvd
      have hfF : ∀ (b : F) (k : Polynomial F), f ≠ Polynomial.C b * k ^ p := hfnd p hp hpe
      have hfmap : ∀ (b : E) (k : Polynomial E), fE ≠ Polynomial.C b * k ^ p := by
        rw [hfE]
        exact Commons.FieldTheory.FiniteField.not_const_mul_pow_map p hp hchar f hfF
      have h2 : fE = Polynomial.C (c⁻¹ * a) * h ^ p := by
        have h3 := congrArg (fun q0 : Polynomial E => Polynomial.C c⁻¹ * q0) hcon
        rw [hg'] at h3
        have h4 : Polynomial.C c⁻¹ * (Polynomial.C c * fE) = fE := by
          rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hcne, Polynomial.C_1, one_mul]
        have h5 : Polynomial.C c⁻¹ * (Polynomial.C a * h ^ p)
            = Polynomial.C (c⁻¹ * a) * h ^ p := by
          rw [← mul_assoc, ← Polynomial.C_mul]
        rw [h4, h5] at h3
        exact h3
      exact hfmap (c⁻¹ * a) h h2
    have hCst := hC₀ E hdivE g' hg'deg hg'nd
    have hNcast : (Fintype.card E : ℝ) = (N : ℝ) := by rw [← hN]
    rw [hNcast, ← hset, ncard_setOf_eq_card_filter] at hCst
    exact hCst
  -- zeros of `fE`
  set Z : ℕ := (Finset.univ.filter (fun a : E => fE.eval a = 0)).card with hZdef
  have hZle : Z ≤ d := by
    rw [hZdef]
    have hsub : (Finset.univ.filter (fun a : E => fE.eval a = 0)) ⊆ fE.roots.toFinset := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hfE0]
      exact ha
    calc (Finset.univ.filter (fun a : E => fE.eval a = 0)).card
        ≤ fE.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ fE.roots.card := Multiset.toFinset_card_le _
      _ ≤ fE.natDegree := Polynomial.card_roots' fE
      _ ≤ f.natDegree := by rw [hfE]; exact Polynomial.natDegree_map_le
      _ ≤ d := hfdeg
  have hZN : Z ≤ N := by
    rw [hZdef, hN]
    simpa using Finset.card_le_univ (Finset.univ.filter (fun a : E => fE.eval a = 0))
  have hZ' : (Finset.univ.filter (fun a : E => ¬ (fE.eval a ≠ 0))).card = Z := by
    rw [hZdef]
    congr 1
    ext a
    simp
  have hNu : (Finset.univ : Finset E).card = N := by rw [Finset.card_univ, ← hN]
  have hTsum : ∑ j : Fin e, T j = N - Z := by
    have h1 : ∑ j : Fin e, T j
        = ∑ a : E, ∑ j : Fin e, (if ψ (fE.eval a) = γ ^ (j : ℕ) then (1:ℕ) else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [hTdef]
      rw [Finset.card_filter]
    have h2 : ∀ a : E, (∑ j : Fin e, (if ψ (fE.eval a) = γ ^ (j : ℕ) then (1:ℕ) else 0))
        = (if ψ (fE.eval a) = 0 then (0:ℕ) else 1) := by
      intro a
      by_cases h : ψ (fE.eval a) = 0
      · rw [if_pos h]
        refine Finset.sum_eq_zero (fun j _ => ?_)
        rw [if_neg]
        intro hh
        rw [h] at hh
        exact pow_ne_zero (j : ℕ) hγne hh.symm
      · rw [if_neg h]
        obtain ⟨i, hi, hzi⟩ := hγprim.eq_pow_of_pow_eq_one ((hval a).resolve_left h)
        rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin e)]
        · rw [if_pos hzi.symm]
        · intro b _ hb
          rw [if_neg]
          intro hh
          exact hb (Fin.ext (hγprim.pow_inj b.isLt hi (hh.symm.trans hzi.symm)))
        · intro hmem
          exact absurd (Finset.mem_univ _) hmem
    have h3 : ∑ a : E, (if fE.eval a = 0 then (0:ℕ) else 1) = N - Z := by
      have hcard : ∑ a : E, (if fE.eval a = 0 then (0:ℕ) else 1)
          = (Finset.univ.filter (fun a : E => fE.eval a ≠ 0)).card := by
        rw [Finset.card_filter]
        exact Finset.sum_congr rfl (fun a _ => by by_cases h : fE.eval a = 0 <;> simp [h])
      rw [hcard]
      have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (p := fun a : E => fE.eval a ≠ 0)
      rw [hZ', hNu] at hsplit
      exact Nat.eq_sub_of_add_eq hsplit
    have h4 : ∑ a : E, (if ψ (fE.eval a) = 0 then (0:ℕ) else 1)
        = ∑ a : E, (if fE.eval a = 0 then (0:ℕ) else 1) := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      by_cases h : ψ (fE.eval a) = 0
      · rw [if_pos h, if_pos ((hψzero (fE.eval a)).mp h)]
      · rw [if_neg h, if_neg (fun hh => h ((hψzero (fE.eval a)).mpr hh))]
    rw [h1, Finset.sum_congr rfl (fun a _ => h2 a), h4, h3]
  -- final estimate
  have hγne1 : γ ≠ 1 := by
    intro h
    have h1 : orderOf γ = 1 := by rw [h, orderOf_one]
    rw [hordγ] at h1
    omega
  have hsumγ : ∑ j : Fin e, γ ^ (j : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range, geomSum_rootOfUnity hγe, if_neg hγne1]
  have hγnorm : ∀ j : Fin e, ‖γ ^ (j : ℕ)‖ = 1 := by
    intro j
    apply Complex.norm_eq_one_of_pow_eq_one
    · rw [← pow_mul, mul_comm, pow_mul, hγe, one_pow]
    · exact he0
  have hcast : ∀ j : Fin e, ‖(T j : ℂ) - ((((N - Z : ℕ) : ℝ) / (e : ℝ) : ℝ) : ℂ)‖
      = |(T j : ℝ) - ((N - Z : ℕ) : ℝ) / (e : ℝ)| := by
    intro j
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, norm_ofReal_eq_abs]
  have hsumZ : ∑ j : Fin e, (T j : ℝ) = ((N - Z : ℕ) : ℝ) := by
    rw [← Nat.cast_sum, hTsum, Nat.cast_sub hZN]
  have hbound : ∀ j : Fin e,
      |(T j : ℝ) - ((N - Z : ℕ) : ℝ) / (e : ℝ)| ≤
        (Z : ℝ) + ((e : ℝ) - 1) * C₀ * Real.sqrt (N : ℝ) := by
    intro j
    have heR : (2 : ℝ) ≤ e := by exact_mod_cast he
    have hZR : (0 : ℝ) ≤ Z := Nat.cast_nonneg Z
    have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
      rw [Real.one_le_sqrt]; exact_mod_cast (by omega : 1 ≤ N)
    have hup : (T j : ℝ) ≤ (N : ℝ) / e + C₀ * Real.sqrt (N : ℝ) := hT_upper j
    have hcompl : ∑ k ∈ Finset.univ.erase j, (T k : ℝ)
        ≤ ((e : ℝ) - 1) * ((N : ℝ) / e + C₀ * Real.sqrt (N : ℝ)) := by
      have h1 : ∑ k ∈ Finset.univ.erase j, (T k : ℝ)
          ≤ ∑ k ∈ Finset.univ.erase j, ((N : ℝ) / e + C₀ * Real.sqrt (N : ℝ)) :=
        Finset.sum_le_sum (fun k _ => hT_upper k)
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ e), Nat.cast_one] at h1
      exact h1
    have hcompl' : ∑ k ∈ Finset.univ.erase j, (T k : ℝ)
        ≤ ((e : ℝ) - 1) * ((N : ℝ) / e) + ((e : ℝ) - 1) * (C₀ * Real.sqrt (N : ℝ)) := by
      calc ∑ k ∈ Finset.univ.erase j, (T k : ℝ)
          ≤ ((e : ℝ) - 1) * ((N : ℝ) / e + C₀ * Real.sqrt (N : ℝ)) := hcompl
        _ = ((e : ℝ) - 1) * ((N : ℝ) / e) + ((e : ℝ) - 1) * (C₀ * Real.sqrt (N : ℝ)) := by
            ring
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin e)) (fun j => (T j : ℝ))
      (Finset.mem_univ j)
    have hTj : (T j : ℝ) = ((N - Z : ℕ) : ℝ) - ∑ k ∈ Finset.univ.erase j, (T k : ℝ) := by
      rw [← hsumZ]
      linarith only [hsplit]
    have hZN' : ((N - Z : ℕ) : ℝ) = (N : ℝ) - (Z : ℝ) := Nat.cast_sub hZN
    have heRpos : (0 : ℝ) < e := by linarith only [heR]
    rw [abs_le]
    constructor
    · -- lower bound
      have hZle' : ((e : ℝ) - 1) * (Z : ℝ) / e ≤ (Z : ℝ) := by
        rw [div_le_iff₀ heRpos]
        linarith only [heR, hZR]
      have h6 : -((Z : ℝ) + ((e : ℝ) - 1) * C₀ * Real.sqrt (N : ℝ))
          ≤ ((N : ℝ) - (Z : ℝ)) - ((e : ℝ) - 1) * ((N : ℝ) / e + C₀ * Real.sqrt (N : ℝ))
            - ((N : ℝ) - (Z : ℝ)) / e := by
        have hkey : ((N : ℝ) - (Z : ℝ)) - ((e : ℝ) - 1) * ((N : ℝ) / e + C₀ * Real.sqrt (N : ℝ))
            - ((N : ℝ) - (Z : ℝ)) / e
            = -(((e : ℝ) - 1) * (Z : ℝ) / e) - ((e : ℝ) - 1) * (C₀ * Real.sqrt (N : ℝ)) := by
          field_simp
          ring
        rw [hkey]
        linarith only [hZle']
      have h5 : ((N : ℝ) - (Z : ℝ)) - ((e : ℝ) - 1) * ((N : ℝ) / e + C₀ * Real.sqrt (N : ℝ))
          - ((N : ℝ) - (Z : ℝ)) / e
          ≤ ((N : ℝ) - (Z : ℝ)) - (∑ k ∈ Finset.univ.erase j, (T k : ℝ))
            - ((N : ℝ) - (Z : ℝ)) / e := by
        linarith only [hcompl', hcompl]
      rw [hTj, hZN']
      linarith only [h5, h6, hcompl]
    · -- upper bound
      have h7 : ((N : ℝ) / e + C₀ * Real.sqrt (N : ℝ)) - ((N : ℝ) - (Z : ℝ)) / e
          = (Z : ℝ) / e + C₀ * Real.sqrt (N : ℝ) := by
        field_simp
        ring
      have h8 : (Z : ℝ) / e + C₀ * Real.sqrt (N : ℝ)
          ≤ (Z : ℝ) + ((e : ℝ) - 1) * C₀ * Real.sqrt (N : ℝ) := by
        have h9 : (Z : ℝ) / e ≤ (Z : ℝ) := by
          rw [div_le_iff₀ heRpos]
          nlinarith only [heR, hZR]
        have h10 : C₀ * Real.sqrt (N : ℝ) ≤ ((e : ℝ) - 1) * (C₀ * Real.sqrt (N : ℝ)) := by
          have h11 : (1 : ℝ) ≤ (e : ℝ) - 1 := by linarith only [heR]
          calc C₀ * Real.sqrt (N : ℝ) = 1 * (C₀ * Real.sqrt (N : ℝ)) := (one_mul _).symm
            _ ≤ ((e : ℝ) - 1) * (C₀ * Real.sqrt (N : ℝ)) :=
                mul_le_mul_of_nonneg_right h11 (mul_nonneg (le_of_lt hC₀pos) (Real.sqrt_nonneg _))
        linarith only [h9, h10]
      rw [hTj, hZN']
      linarith only [hup, h7, h8, hTj, hsumZ, hsplit, hZN']
  -- put everything together
  have hmain : ‖∑ a : E, ψ (fE.eval a)‖
      ≤ ((e : ℝ) * (d : ℝ) + (e : ℝ) * ((e : ℝ) - 1) * C₀) * Real.sqrt (N : ℝ) := by
    rw [hdecomp]
    set cr : ℂ := ((((N - Z : ℕ) : ℝ) / (e : ℝ) : ℝ) : ℂ) with hcr
    have hshift : (∑ j : Fin e, γ ^ (j : ℕ) * (T j : ℂ))
        = (∑ j : Fin e, γ ^ (j : ℕ) * ((T j : ℂ) - cr)) := by
      have hexp : ∑ j : Fin e, γ ^ (j : ℕ) * ((T j : ℂ) - cr)
          = (∑ j : Fin e, γ ^ (j : ℕ) * (T j : ℂ)) - (∑ j : Fin e, γ ^ (j : ℕ)) * cr := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [hexp, hsumγ, zero_mul, sub_zero]
    rw [hshift]
    calc ‖∑ j : Fin e, γ ^ (j : ℕ) * ((T j : ℂ) - cr)‖
        ≤ ∑ j : Fin e, ‖γ ^ (j : ℕ) * ((T j : ℂ) - cr)‖ := norm_sum_le _ _
      _ = ∑ j : Fin e, |(T j : ℝ) - ((N - Z : ℕ) : ℝ) / (e : ℝ)| := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [norm_mul, hγnorm j, one_mul, hcr, hcast j]
      _ ≤ ∑ _j : Fin e, ((Z : ℝ) + ((e : ℝ) - 1) * C₀ * Real.sqrt (N : ℝ)) :=
          Finset.sum_le_sum (fun j _ => hbound j)
      _ = (e : ℝ) * ((Z : ℝ) + ((e : ℝ) - 1) * C₀ * Real.sqrt (N : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ((e : ℝ) * (d : ℝ) + (e : ℝ) * ((e : ℝ) - 1) * C₀) * Real.sqrt (N : ℝ) := by
          have heR : (2 : ℝ) ≤ e := by exact_mod_cast he
          have hdR : (0 : ℝ) ≤ d := by exact_mod_cast (by omega : 0 ≤ d)
          have heRpos : (0 : ℝ) < e := by linarith only [heR]
          have hZN'' : (Z : ℝ) ≤ (d : ℝ) := by exact_mod_cast hZle
          have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
            rw [Real.one_le_sqrt]; exact_mod_cast (by omega : 1 ≤ N)
          have h1 : (d : ℝ) ≤ (d : ℝ) * Real.sqrt (N : ℝ) := by
            calc (d : ℝ) = (d : ℝ) * 1 := (mul_one _).symm
              _ ≤ (d : ℝ) * Real.sqrt (N : ℝ) := mul_le_mul_of_nonneg_left hsqrt1 hdR
          have h2 : (Z : ℝ) ≤ (d : ℝ) * Real.sqrt (N : ℝ) := le_trans hZN'' h1
          have h3 : (e : ℝ) * (Z : ℝ) ≤ (e : ℝ) * ((d : ℝ) * Real.sqrt (N : ℝ)) :=
            mul_le_mul_of_nonneg_left h2 (le_of_lt heRpos)
          have hgoal : (e : ℝ) * ((Z : ℝ) + ((e : ℝ) - 1) * C₀ * Real.sqrt (N : ℝ))
              = (e : ℝ) * (Z : ℝ) + ((e : ℝ) * ((e : ℝ) - 1) * C₀) * Real.sqrt (N : ℝ) := by
            ring
          have hgoal2 : ((e : ℝ) * (d : ℝ) + (e : ℝ) * ((e : ℝ) - 1) * C₀) * Real.sqrt (N : ℝ)
              = (e : ℝ) * ((d : ℝ) * Real.sqrt (N : ℝ))
                + ((e : ℝ) * ((e : ℝ) - 1) * C₀) * Real.sqrt (N : ℝ) := by ring
          rw [hgoal, hgoal2]
          linarith only [h3]
  rw [← hsqrtN]
  calc ‖∑ a : E, χ (Algebra.norm F (fE.eval a))‖
      = ‖∑ a : E, ψ (fE.eval a)‖ := by
        congr 1
        exact Finset.sum_congr rfl (fun a _ => (hψapply (fE.eval a)).symm)
    _ ≤ _ := hmain
end Main

end Commons.NumberTheory.CharacterSum
