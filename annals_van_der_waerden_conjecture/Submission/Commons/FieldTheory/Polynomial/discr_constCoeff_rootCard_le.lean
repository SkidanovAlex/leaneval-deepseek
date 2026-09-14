import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Submission.Commons.FieldTheory.Polynomial.discr_eq_zero_iff_not_separable

open Polynomial
open scoped BigOperators

set_option autoImplicit false

/-! Root count: for a monic polynomial `f` of degree `n` over a field `F` of
characteristic not dividing `n`, varying only the constant coefficient `c`, at most
`n - 1` values of `c` make the discriminant vanish.

Mathematical proof sketch (multiple roots, avoids determinant analysis):
`Disc(f_c) = 0` iff `f_c` is inseparable (commons `discr_eq_zero_iff_not_separable`,
valid since `f_c` stays monic of degree `n`), iff `gcd f_c f_c'` is a non-unit
(`EuclideanDomain.gcd_isUnit_iff`), i.e. of positive degree (`isUnit_iff_degree_eq_zero`),
so over `K = AlgebraicClosure F` it has a root `a` (`IsAlgClosed.exists_root`), which is
then a common root of `f_c` and `f_c'` over `K`.  But `f_c' = f'` does not depend on `c`
(a constant change is killed by the derivative); so every counted `c` yields a root `a`
of `(f'.map (algebraMap F K))`, and `a` determines `c` back via `(f_c.map φ).eval a = 0`
(φ injective), so distinct `c` give distinct roots of `f'`.  The number of roots of a
nonzero polynomial is at most its `natDegree` (`Polynomial.ncard_rootSet_le`), and the
degree of `f'` is at most `n - 1` (`natDegree_derivative_le`); the characteristic
hypothesis `(n : F) ≠ 0` guarantees `f' ≠ 0`. -/

namespace Commons.FieldTheory.Polynomial

noncomputable section

variable {F : Type*} [Field F]

private lemma fc_eq_add_C (f : F[X]) (c : F) :
    f - C (f.coeff 0) + C c = f + C (c - f.coeff 0) := by
  calc
    f - C (f.coeff 0) + C c = f + (C c - C (f.coeff 0)) := by ring
    _ = f + C (c - f.coeff 0) := by
      rw [← map_sub]

/-- Changing only the constant coefficient keeps a polynomial of degree at least `2` monic
of the same degree. -/
private lemma constCoeff_Monic_natDegree (f : F[X]) (hf : f.Monic) (hn : 2 ≤ f.natDegree)
    (c : F) :
    (f - C (f.coeff 0) + C c).Monic ∧
      (f - C (f.coeff 0) + C c).natDegree = f.natDegree := by
  classical
  rw [fc_eq_add_C]
  have hdegC : (C (c - f.coeff 0) : F[X]).natDegree < f.natDegree := by
    rw [natDegree_C]
    exact lt_of_lt_of_le (by decide : 0 < 2) hn
  constructor
  · rw [Monic, leadingCoeff, natDegree_add_eq_left_of_natDegree_lt hdegC, coeff_add]
    have hc0 : (C (c - f.coeff 0) : F[X]).coeff f.natDegree = 0 := by
      rw [Polynomial.coeff_C]
      simp [ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hn)]
    rw [hc0, add_zero]
    exact hf.coeff_natDegree
  · exact natDegree_add_eq_left_of_natDegree_lt hdegC

/-- The derivative kills the constant term: `f_c' = f'`. -/
private lemma derivative_constCoeff (f : F[X]) (c : F) :
    (f - C (f.coeff 0) + C c).derivative = f.derivative := by
  rw [fc_eq_add_C]
  simp [Polynomial.derivative_add, Polynomial.derivative_C]

/-- Evaluating the constant-perturbed polynomial over an extension: `c` is recovered from
the value of the map at a root. -/
private lemma map_eval_constCoeff (K : Type*) [Field K] (φ : F →+* K) (f : F[X])
    (c : F) (a : K) :
    Polynomial.eval a ((f - C (f.coeff 0) + C c).map φ) =
      eval a (f.map φ) - φ (f.coeff 0) + φ c := by
  rw [fc_eq_add_C]
  rw [Polynomial.map_add, Polynomial.map_C]
  rw [Polynomial.eval_add, Polynomial.eval_C]
  rw [map_sub]
  ring

/-- Since `(n : F) ≠ 0`, the derivative of a monic degree-`n` polynomial is nonzero
(its coefficient of degree `n - 1` is `n`). -/
private lemma derivative_ne_zero_of_char (f : F[X]) (hf : f.Monic) (hn : 2 ≤ f.natDegree)
    (hchar : (f.natDegree : F) ≠ 0) : f.derivative ≠ 0 := by
  have hk : (f.natDegree - 1) + 1 = f.natDegree := by omega
  have hcast : ((↑(f.natDegree - 1) : F) + 1) = (f.natDegree : F) := by
    calc
      (↑(f.natDegree - 1) : F) + 1 = (↑(f.natDegree - 1) : F) + (↑(1 : ℕ) : F) := by simp
      _ = (↑((f.natDegree - 1) + 1) : F) := by rw [← Nat.cast_add]
      _ = (↑f.natDegree : F) := by rw [hk]
  have hc_eq : f.derivative.coeff (f.natDegree - 1) = (f.natDegree : F) := by
    rw [Polynomial.coeff_derivative]
    rw [show (f.natDegree - 1) + 1 = f.natDegree by omega]
    rw [hf.coeff_natDegree]
    rw [hcast]
    simp
  intro hd0
  have hzero : f.derivative.coeff (f.natDegree - 1) = 0 := by rw [hd0]; simp
  exact hchar (hc_eq.symm.trans hzero)

/-- If the discriminant of `f_c` vanishes then `f_c` and `f'` have a common root over the
algebraic closure of `F`. -/
private lemma exists_common_root (f : F[X]) (hf : f.Monic) (hn : 2 ≤ f.natDegree)
    {c : F} (hc : Polynomial.discr (f - C (f.coeff 0) + C c) = 0) :
    ∃ a : AlgebraicClosure F,
      Polynomial.eval a (((f - C (f.coeff 0) + C c).map
        (algebraMap F (AlgebraicClosure F)))) = 0 ∧
      Polynomial.eval a ((f.derivative).map (algebraMap F (AlgebraicClosure F))) = 0 := by
  classical
  let K := AlgebraicClosure F
  let φ : F →+* K := algebraMap F K
  let fc : F[X] := f - C (f.coeff 0) + C c
  have hfc_monic : fc.Monic := (constCoeff_Monic_natDegree f hf hn c).1
  have hfc_ne0 : fc ≠ 0 := hfc_monic.ne_zero
  have hfc_deg_pos : 0 < fc.natDegree := by
    rw [(constCoeff_Monic_natDegree f hf hn c).2]
    omega
  have hdisc : Polynomial.discr fc = 0 := by simpa [fc] using hc
  have hnotsep : ¬ fc.Separable :=
    (discr_eq_zero_iff_not_separable (p := fc) hfc_monic hfc_deg_pos).mp hdisc
  have hnotcop : ¬ IsCoprime fc (derivative fc) := by
    intro hcop
    exact hnotsep ((separable_def fc).mpr hcop)
  have hderiv : derivative fc = f.derivative := by
    change derivative (f - C (f.coeff 0) + C c) = f.derivative
    exact derivative_constCoeff f c
  have hnotcop' : ¬ IsCoprime fc (f.derivative) := by
    simp [hderiv] at hnotcop
    exact hnotcop
  let g : F[X] := EuclideanDomain.gcd fc (f.derivative)
  have hg_not_unit : ¬ IsUnit g := by
    intro hu
    exact hnotcop' ((EuclideanDomain.gcd_isUnit_iff).mp hu)
  have hg_ne0 : g ≠ 0 := by
    intro hg0
    have hdvd : g ∣ fc := EuclideanDomain.gcd_dvd_left fc (f.derivative)
    rw [hg0] at hdvd
    exact hfc_ne0 (zero_dvd_iff.mp hdvd)
  have hdeg_g_ne : g.degree ≠ 0 := by
    intro hd0
    exact hg_not_unit ((Polynomial.isUnit_iff_degree_eq_zero).mpr hd0)
  have hnd_g_ne : g.natDegree ≠ 0 := by
    intro hnd0
    apply hdeg_g_ne
    rw [Polynomial.degree_eq_natDegree hg_ne0, hnd0]
    simp
  have hφi : Function.Injective (φ : F → K) := by
    exact RingHom.injective (algebraMap F K)
  let gm : K[X] := g.map φ
  have hgm_ne0 : gm ≠ 0 := (Polynomial.map_ne_zero_iff hφi).mpr hg_ne0
  have hnd_gm : gm.natDegree = g.natDegree := Polynomial.natDegree_map_eq_of_injective hφi g
  have hnd_gm_ne : gm.natDegree ≠ 0 := by rwa [hnd_gm]
  have hnd_gm_pos : 0 < gm.natDegree := Nat.pos_of_ne_zero hnd_gm_ne
  have hdeg_gm_pos : 0 < gm.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos]
    exact hnd_gm_pos
  rcases IsAlgClosed.exists_root (p := gm) (ne_of_gt hdeg_gm_pos) with ⟨a, ha⟩
  rcases (EuclideanDomain.gcd_dvd_left fc (f.derivative)) with ⟨r, hr⟩
  have ha_fc : Polynomial.eval a (fc.map φ) = 0 := by
    calc
      Polynomial.eval a (fc.map φ) = Polynomial.eval a ((g * r).map φ) := by rw [← hr]
      _ = Polynomial.eval a (g.map φ * r.map φ) := by rw [Polynomial.map_mul]
      _ = Polynomial.eval a (g.map φ) * Polynomial.eval a (r.map φ) := by
        rw [Polynomial.eval_mul]
      _ = 0 := by rw [ha]; simp
  rcases (EuclideanDomain.gcd_dvd_right fc (f.derivative)) with ⟨s, hs⟩
  have ha_der : Polynomial.eval a ((f.derivative).map φ) = 0 := by
    calc
      Polynomial.eval a ((f.derivative).map φ) = Polynomial.eval a ((g * s).map φ) := by
        rw [← hs]
      _ = Polynomial.eval a (g.map φ * s.map φ) := by rw [Polynomial.map_mul]
      _ = Polynomial.eval a (g.map φ) * Polynomial.eval a (s.map φ) := by
        rw [Polynomial.eval_mul]
      _ = 0 := by rw [ha]; simp
  refine ⟨a, ?_, ?_⟩
  · simpa [K, φ, fc] using ha_fc
  · simpa [K, φ] using ha_der

/-- For a monic polynomial `f` of degree `n` over a field `F` whose characteristic does not
divide `n`, varying only the constant coefficient `c`, at most `n - 1` values of `c` make the
discriminant vanish. -/
theorem discr_constCoeff_rootCard_le {F : Type*} [Field F] [Fintype F] (f : F[X])
    (hf : f.Monic) (hn : 2 ≤ f.natDegree) (hchar : (f.natDegree : F) ≠ 0) :
    ({c : F | Polynomial.discr (f - Polynomial.C (f.coeff 0) + Polynomial.C c) = 0} : Set F).ncard ≤
      f.natDegree - 1 := by
  classical
  let K := AlgebraicClosure F
  let φ : F →+* K := algebraMap F K
  let n : ℕ := f.natDegree
  let S : Set F := {c : F | Polynomial.discr (f - Polynomial.C (f.coeff 0) + Polynomial.C c) = 0}
  let T : Set K := (f.derivative).rootSet K
  change S.ncard ≤ n - 1
  have hφi : Function.Injective (φ : F → K) := by
    exact RingHom.injective (algebraMap F K)
  have hderiv_ne : f.derivative ≠ 0 := derivative_ne_zero_of_char f hf hn hchar
  let ρ : F → K := fun c => if hc : c ∈ S then Classical.choose (exists_common_root f hf hn hc) else 0
  have hρ_maps : ∀ c ∈ S, ρ c ∈ T := by
    intro c hc
    have hroot := Classical.choose_spec (exists_common_root f hf hn hc)
    have hmem :
        (Classical.choose (exists_common_root f hf hn hc)) ∈ (f.derivative).rootSet K := by
      rw [Polynomial.mem_rootSet']
      refine ⟨(Polynomial.map_ne_zero_iff hφi).mpr hderiv_ne, ?_⟩
      rw [aeval_def, eval₂_eq_eval_map]
      simpa [K, φ] using hroot.2
    simpa [ρ, hc, T] using hmem
  have hρ_inj : Set.InjOn ρ S := by
    intro c₁ hc₁ c₂ hc₂ hρ
    let a₁ : K := Classical.choose (exists_common_root f hf hn hc₁)
    let a₂ : K := Classical.choose (exists_common_root f hf hn hc₂)
    have ha_eq : a₁ = a₂ := by
      simpa [ρ, a₁, a₂, hc₁, hc₂] using hρ
    have hroot1 := Classical.choose_spec (exists_common_root f hf hn hc₁)
    have hroot2 := Classical.choose_spec (exists_common_root f hf hn hc₂)
    have h1 : eval a₁ (f.map φ) - φ (f.coeff 0) + φ c₁ = 0 := by
      rw [← map_eval_constCoeff K φ f c₁ a₁]
      simpa [a₁, K, φ] using hroot1.1
    have h2 : eval a₁ (f.map φ) - φ (f.coeff 0) + φ c₂ = 0 := by
      rw [← map_eval_constCoeff K φ f c₂ a₁]
      have h2' : eval a₂ ((f - C (f.coeff 0) + C c₂).map φ) = 0 := by
        simpa [a₂, K, φ] using hroot2.1
      simpa [ha_eq] using h2'
    have hdiff : φ c₁ - φ c₂ = 0 := by
      calc
        φ c₁ - φ c₂ = (eval a₁ (f.map φ) - φ (f.coeff 0) + φ c₁) -
            (eval a₁ (f.map φ) - φ (f.coeff 0) + φ c₂) := by ring
        _ = 0 - 0 := by rw [h1, h2]
        _ = 0 := by ring
    exact hφi (sub_eq_zero.mp hdiff)
  have hST : S.ncard ≤ T.ncard := by
    exact Set.ncard_le_ncard_of_injOn ρ hρ_maps hρ_inj
      (Polynomial.rootSet_finite (f.derivative) K)
  have hT_le : T.ncard ≤ (f.derivative).natDegree := by
    simpa [T] using (Polynomial.ncard_rootSet_le (f.derivative) K)
  have hT_bound : T.ncard ≤ n - 1 := by
    exact le_trans hT_le (Polynomial.natDegree_derivative_le f)
  exact le_trans hST hT_bound

end

end Commons.FieldTheory.Polynomial
