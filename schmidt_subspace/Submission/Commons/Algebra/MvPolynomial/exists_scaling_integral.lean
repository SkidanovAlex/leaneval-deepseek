import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Nat.Cast.Field

/-!
# Splitting an integral product of rational polynomials up to a scalar

Given `U₁ ∈ ℚ[x]`, `U₂ ∈ ℚ[y]` (with `x` ranging over `ι`, `y` over `κ`) whose product
`U₁(x)·U₂(y)` is (the image of) an integral polynomial `V ∈ ℤ[x,y]`, there is a non-zero
rational `c` such that `c⁻¹·U₁` and `c·U₂` are both integral.

This is the classical "clearing denominators / Gauss content" fact: writing
`U₁ = a₁ P₁`, `U₂ = a₂ P₂` with `P₁, P₂` primitive integral polynomials, integrality of the
product forces `a₁ a₂ ∈ ℤ`, and then `c = a₁` (or `c = a₂⁻¹`) works.
-/

namespace Commons.Algebra.MvPolynomial

open _root_.MvPolynomial

namespace ScalingAux

/-- Given a common denominator `B` of the rational `r` (i.e. `r.den ∣ B`), the integer
`B * r` expressed explicitly as `(B / r.den) * r.num` (with `r.den` a divisor of `B`). -/
noncomputable def aa (B : ℕ) (r : ℚ) : ℤ := ((B / r.den : ℕ) : ℤ) * r.num

lemma aa_spec {B : ℕ} {r : ℚ} (h : r.den ∣ B) : (aa B r : ℚ) = (B : ℚ) * r := by
  have hden : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Rat.den_nz r)
  have hnum : (r.num : ℚ) = r * (r.den : ℚ) := (div_eq_iff hden).mp (Rat.num_div_den r)
  rw [aa, Int.cast_mul, Int.cast_natCast, Nat.cast_div h hden, hnum]
  field_simp

/-- **Rational scaling lemma.** For finite non-empty sets `R, S ⊆ ℚ \ {0}` such that every
product `r * s` (`r ∈ R`, `s ∈ S`) is an integer, there is a non-zero `c ∈ ℚ` making every
`c⁻¹ * r` (`r ∈ R`) and every `c * s` (`s ∈ S`) an integer. -/
theorem exists_rat_scaling (R S : Finset ℚ)
    (hRne : R.Nonempty) (_hSne : S.Nonempty)
    (hR0 : ∀ r ∈ R, r ≠ 0) (_hS0 : ∀ s ∈ S, s ≠ 0)
    (h : ∀ r ∈ R, ∀ s ∈ S, ∃ z : ℤ, (z : ℚ) = r * s) :
    ∃ c : ℚ, c ≠ 0 ∧
      (∀ r ∈ R, ∃ z : ℤ, (z : ℚ) = c⁻¹ * r) ∧
      (∀ s ∈ S, ∃ z : ℤ, (z : ℚ) = c * s) := by
  classical
  set B : ℕ := ∏ r ∈ R, r.den with hBdef
  set C : ℕ := ∏ s ∈ S, s.den with hCdef
  have hBden : ∀ r ∈ R, r.den ∣ B := by
    intro r hr; rw [hBdef]; exact Finset.dvd_prod_of_mem (fun r => r.den) hr
  have hCden : ∀ s ∈ S, s.den ∣ C := by
    intro s hs; rw [hCdef]; exact Finset.dvd_prod_of_mem (fun s => s.den) hs
  have hBpos : 0 < B := by
    rw [hBdef]; exact Finset.prod_pos (fun r _ => Rat.den_pos r)
  have hCpos : 0 < C := by
    rw [hCdef]; exact Finset.prod_pos (fun s _ => Rat.den_pos s)
  have hBne : (B : ℚ) ≠ 0 := by exact_mod_cast hBpos.ne'
  have hCne : (C : ℚ) ≠ 0 := by exact_mod_cast hCpos.ne'
  have haa_spec : ∀ r ∈ R, (aa B r : ℚ) = (B : ℚ) * r := fun r hr => aa_spec (hBden r hr)
  have hbb_spec : ∀ s ∈ S, (aa C s : ℚ) = (C : ℚ) * s := fun s hs => aa_spec (hCden s hs)
  have haa_ne : ∀ r ∈ R, aa B r ≠ 0 := by
    intro r hr h0
    have h1 : (aa B r : ℚ) = 0 := by rw [h0]; simp
    rw [haa_spec r hr] at h1
    exact mul_ne_zero hBne (hR0 r hr) h1
  set G : ℤ := R.gcd (aa B) with hGdef
  have hGne : G ≠ 0 := by
    rw [hGdef]
    intro h0
    rw [Finset.gcd_eq_zero_iff] at h0
    obtain ⟨r, hr⟩ := hRne
    exact haa_ne r hr (h0 r hr)
  have hGne' : (G : ℚ) ≠ 0 := by exact_mod_cast hGne
  refine ⟨(G : ℚ) / (B : ℚ), ?_, ?_, ?_⟩
  · exact div_ne_zero hGne' hBne
  · intro r hr
    have hdvd : G ∣ aa B r := by rw [hGdef]; exact Finset.gcd_dvd (s := R) (f := aa B) hr
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k, ?_⟩
    have h1 : (aa B r : ℚ) = (B : ℚ) * r := haa_spec r hr
    have h2 : (aa B r : ℚ) = (G : ℚ) * k := by rw [hk]; simp
    have h3 : (B : ℚ) * r = (G : ℚ) * k := by rw [← h1, h2]
    have hcalc : ((G : ℚ) / (B : ℚ))⁻¹ * r = (k : ℚ) := by
      calc ((G : ℚ) / (B : ℚ))⁻¹ * r = ((B : ℚ) / (G : ℚ)) * r := by rw [inv_div]
        _ = (B : ℚ) * r / (G : ℚ) := by rw [div_mul_eq_mul_div]
        _ = (G : ℚ) * k / (G : ℚ) := by rw [h3]
        _ = (k : ℚ) := mul_div_cancel_left₀ (k : ℚ) hGne'
    exact hcalc.symm
  · intro s hs
    have hdvd_each : ∀ r ∈ R, ((B : ℤ) * (C : ℤ)) ∣ aa B r * aa C s := by
      intro r hr
      obtain ⟨z, hz⟩ := h r hr s hs
      refine ⟨z, ?_⟩
      have hkey : ((aa B r * aa C s : ℤ) : ℚ) = (((B:ℤ) * (C:ℤ) * z : ℤ) : ℚ) := by
        rw [Int.cast_mul, Int.cast_mul, Int.cast_mul, haa_spec r hr, hbb_spec s hs, hz]
        push_cast
        ring
      exact Int.cast_injective hkey
    have hdvd_gcd : ((B : ℤ) * (C : ℤ)) ∣ R.gcd (fun r => aa B r * aa C s) :=
      Finset.dvd_gcd (fun r hr => hdvd_each r hr)
    have hassoc : R.gcd (fun r => aa B r * aa C s) = R.gcd (fun r => aa C s * aa B r) :=
      Finset.gcd_congr rfl (fun r _ => mul_comm _ _)
    rw [hassoc] at hdvd_gcd
    have hA : Associated (R.gcd (fun r => aa C s * aa B r)) (aa C s * G) := by
      have hh := Finset.gcd_mul_left' R (aa B) (aa C s)
      rwa [← hGdef] at hh
    have hdvd2 : ((B : ℤ) * (C : ℤ)) ∣ aa C s * G := (hA.dvd_iff_dvd_right).mp hdvd_gcd
    have hdvd3 : ((B : ℤ) * (C : ℤ)) ∣ G * aa C s := by
      rw [mul_comm G (aa C s)]
      exact hdvd2
    obtain ⟨k, hk⟩ := hdvd3
    refine ⟨k, ?_⟩
    have hBC : (B : ℚ) * (C : ℚ) ≠ 0 := mul_ne_zero hBne hCne
    have hs_eq : s = (aa C s : ℚ) / (C : ℚ) := by
      rw [hbb_spec s hs, mul_div_cancel_left₀ s hCne]
    have hkey' : (G : ℚ) * (aa C s : ℚ) = (B : ℚ) * (C : ℚ) * (k : ℚ) := by
      have hc := congrArg (fun z : ℤ => (z : ℚ)) hk
      push_cast at hc
      simpa using hc
    have hcalc : ((G : ℚ) / (B : ℚ)) * s = (k : ℚ) := by
      calc ((G : ℚ) / (B : ℚ)) * s
          = ((G : ℚ) / (B : ℚ)) * ((aa C s : ℚ) / (C : ℚ)) :=
              congrArg (fun x => ((G : ℚ) / (B : ℚ)) * x) hs_eq
        _ = (G : ℚ) * (aa C s : ℚ) / ((B : ℚ) * (C : ℚ)) := by rw [div_mul_div_comm]
        _ = (B : ℚ) * (C : ℚ) * (k : ℚ) / ((B : ℚ) * (C : ℚ)) := by rw [hkey']
        _ = (k : ℚ) := mul_div_cancel_left₀ (k : ℚ) hBC
    exact hcalc.symm

/-- Coefficient of the product of two polynomials in disjoint variable sets, at a monomial
that splits as `m` (on the `ι` side) and `n` (on the `κ` side). -/
theorem coeff_mul_rename_inl_inr {ι κ : Type*} (U₁ : MvPolynomial ι ℚ)
    (U₂ : MvPolynomial κ ℚ) (m : ι →₀ ℕ) (n : κ →₀ ℕ) :
    MvPolynomial.coeff (m.mapDomain Sum.inl + n.mapDomain Sum.inr)
        (MvPolynomial.rename Sum.inl U₁ * MvPolynomial.rename Sum.inr U₂)
      = MvPolynomial.coeff m U₁ * MvPolynomial.coeff n U₂ := by
  classical
  rw [MvPolynomial.coeff_mul]
  set x₀ : ((ι ⊕ κ) →₀ ℕ) × ((ι ⊕ κ) →₀ ℕ) :=
    (m.mapDomain (Sum.inl : ι → ι ⊕ κ), n.mapDomain (Sum.inr : κ → ι ⊕ κ)) with hx₀
  rw [Finset.sum_eq_single x₀]
  · have e1 : x₀.1 = m.mapDomain (Sum.inl : ι → ι ⊕ κ) := by rw [hx₀]
    have e2 : x₀.2 = n.mapDomain (Sum.inr : κ → ι ⊕ κ) := by rw [hx₀]
    rw [e1, e2, coeff_rename_mapDomain Sum.inl Sum.inl_injective,
        coeff_rename_mapDomain Sum.inr Sum.inr_injective]
  · intro x hx hxne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_contra hcon
    have h1 : MvPolynomial.coeff x.1 (MvPolynomial.rename Sum.inl U₁) ≠ 0 :=
      fun h => hcon (by rw [h, zero_mul])
    have h2 : MvPolynomial.coeff x.2 (MvPolynomial.rename Sum.inr U₂) ≠ 0 :=
      fun h => hcon (by rw [h, mul_zero])
    obtain ⟨a, ha, -⟩ := coeff_rename_ne_zero Sum.inl U₁ x.1 h1
    obtain ⟨b, hb, -⟩ := coeff_rename_ne_zero Sum.inr U₂ x.2 h2
    have key : a.mapDomain (Sum.inl : ι → ι ⊕ κ) + b.mapDomain (Sum.inr : κ → ι ⊕ κ)
        = m.mapDomain (Sum.inl : ι → ι ⊕ κ) + n.mapDomain (Sum.inr : κ → ι ⊕ κ) := by
      rw [ha, hb, hx]
    have ham : a = m := by
      ext i
      have h1 := congrArg (fun (f : (ι ⊕ κ) →₀ ℕ) => f (Sum.inl i)) key
      simp only [Finsupp.add_apply, Finsupp.mapDomain_apply Sum.inl_injective] at h1
      rw [Finsupp.mapDomain_of_notMem_range b (Sum.inl i)
            (by rintro ⟨j, hj⟩; exact Sum.inl_ne_inr hj.symm)] at h1
      rw [Finsupp.mapDomain_of_notMem_range n (Sum.inl i)
            (by rintro ⟨j, hj⟩; exact Sum.inl_ne_inr hj.symm)] at h1
      simpa using h1
    have hbn : b = n := by
      ext j
      have h1 := congrArg (fun (f : (ι ⊕ κ) →₀ ℕ) => f (Sum.inr j)) key
      simp only [Finsupp.add_apply, Finsupp.mapDomain_apply Sum.inr_injective] at h1
      rw [Finsupp.mapDomain_of_notMem_range a (Sum.inr j)
            (by rintro ⟨i, hi⟩; exact Sum.inr_ne_inl hi.symm)] at h1
      rw [Finsupp.mapDomain_of_notMem_range m (Sum.inr j)
            (by rintro ⟨i, hi⟩; exact Sum.inr_ne_inl hi.symm)] at h1
      simpa using h1
    exact hxne (by
      apply Prod.ext
      · simp [← ha, ham, hx₀]
      · simp [← hb, hbn, hx₀])
  · intro hx
    exact absurd (by rw [Finset.HasAntidiagonal.mem_antidiagonal, hx₀]) hx

/-- A multivariate polynomial over `ℚ` all of whose coefficients are integers is the image of
an integral polynomial. -/
theorem exists_map_eq_of_coeff_int {ι : Type*} (U : MvPolynomial ι ℚ)
    (h : ∀ m : ι →₀ ℕ, ∃ z : ℤ, (z : ℚ) = U.coeff m) :
    ∃ W : MvPolynomial ι ℤ, W.map (Int.castRingHom ℚ) = U := by
  classical
  refine ⟨∑ m ∈ U.support, MvPolynomial.monomial m (Classical.choose (h m)), ?_⟩
  rw [map_sum]
  simp only [MvPolynomial.map_monomial]
  have hc : ∀ m, (Int.castRingHom ℚ) (Classical.choose (h m)) = U.coeff m :=
    fun m => Classical.choose_spec (h m)
  rw [Finset.sum_congr rfl (fun m _ => by rw [hc m])]
  exact (MvPolynomial.as_sum U).symm

end ScalingAux

open ScalingAux

/-- **Main lemma.** If a product of two rational polynomials in disjoint variable sets is
integral, then up to a common scalar both factors are integral. -/
theorem exists_scaling_integral {ι κ : Type*} (U₁ : MvPolynomial ι ℚ) (U₂ : MvPolynomial κ ℚ)
    (h₁ : U₁ ≠ 0) (h₂ : U₂ ≠ 0) (V : MvPolynomial (ι ⊕ κ) ℤ)
    (hV : V.map (Int.castRingHom ℚ) =
      MvPolynomial.rename Sum.inl U₁ * MvPolynomial.rename Sum.inr U₂) :
    ∃ (c : ℚ), c ≠ 0 ∧
      (∃ W₁ : MvPolynomial ι ℤ, W₁.map (Int.castRingHom ℚ) = MvPolynomial.C c⁻¹ * U₁) ∧
      (∃ W₂ : MvPolynomial κ ℤ, W₂.map (Int.castRingHom ℚ) = MvPolynomial.C c * U₂) := by
  classical
  -- Extract the coefficientwise cross condition from `hV`.
  have hcross : ∀ (m : ι →₀ ℕ) (n : κ →₀ ℕ),
      ∃ z : ℤ, (z : ℚ) = MvPolynomial.coeff m U₁ * MvPolynomial.coeff n U₂ := by
    intro m n
    refine ⟨MvPolynomial.coeff (m.mapDomain Sum.inl + n.mapDomain Sum.inr) V, ?_⟩
    have hmap : ((MvPolynomial.coeff (m.mapDomain Sum.inl + n.mapDomain Sum.inr) V : ℤ) : ℚ)
        = MvPolynomial.coeff (m.mapDomain Sum.inl + n.mapDomain Sum.inr)
            ((MvPolynomial.map (Int.castRingHom ℚ)) V) :=
      (MvPolynomial.coeff_map (Int.castRingHom ℚ) V _).symm
    rw [hmap, hV, coeff_mul_rename_inl_inr]
  set R : Finset ℚ := U₁.support.image (fun m => MvPolynomial.coeff m U₁) with hR
  set S : Finset ℚ := U₂.support.image (fun n => MvPolynomial.coeff n U₂) with hS
  have hRne : R.Nonempty := by
    rw [hR]
    obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr h₁
    exact ⟨MvPolynomial.coeff m U₁, Finset.mem_image.mpr ⟨m, hm, rfl⟩⟩
  have hSne : S.Nonempty := by
    rw [hS]
    obtain ⟨n, hn⟩ := MvPolynomial.support_nonempty.mpr h₂
    exact ⟨MvPolynomial.coeff n U₂, Finset.mem_image.mpr ⟨n, hn, rfl⟩⟩
  have hR0 : ∀ r ∈ R, r ≠ 0 := by
    intro r hr
    rw [hR] at hr
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hr
    exact MvPolynomial.mem_support_iff.mp hm
  have hS0 : ∀ s ∈ S, s ≠ 0 := by
    intro s hs
    rw [hS] at hs
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hs
    exact MvPolynomial.mem_support_iff.mp hn
  have hcrossRS : ∀ r ∈ R, ∀ s ∈ S, ∃ z : ℤ, (z : ℚ) = r * s := by
    intro r hr s hs
    rw [hR] at hr; rw [hS] at hs
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hs
    exact hcross m n
  obtain ⟨c, hc0, hcinv, hcmul⟩ := exists_rat_scaling R S hRne hSne hR0 hS0 hcrossRS
  refine ⟨c, hc0, ?_, ?_⟩
  · apply exists_map_eq_of_coeff_int
    intro m
    by_cases hm : m ∈ U₁.support
    · have hmem : MvPolynomial.coeff m U₁ ∈ R := by
        rw [hR]; exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
      obtain ⟨z, hz⟩ := hcinv (MvPolynomial.coeff m U₁) hmem
      exact ⟨z, by rw [MvPolynomial.coeff_C_mul]; exact hz⟩
    · refine ⟨0, ?_⟩
      have h0 : MvPolynomial.coeff m U₁ = 0 := by
        by_contra hc
        exact hm (MvPolynomial.mem_support_iff.mpr hc)
      rw [MvPolynomial.coeff_C_mul, h0, mul_zero]
      simp
  · apply exists_map_eq_of_coeff_int
    intro n
    by_cases hn : n ∈ U₂.support
    · have hmem : MvPolynomial.coeff n U₂ ∈ S := by
        rw [hS]; exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
      obtain ⟨z, hz⟩ := hcmul (MvPolynomial.coeff n U₂) hmem
      exact ⟨z, by rw [MvPolynomial.coeff_C_mul]; exact hz⟩
    · refine ⟨0, ?_⟩
      have h0 : MvPolynomial.coeff n U₂ = 0 := by
        by_contra hc
        exact hn (MvPolynomial.mem_support_iff.mpr hc)
      rw [MvPolynomial.coeff_C_mul, h0, mul_zero]
      simp

end Commons.Algebra.MvPolynomial