import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.CharCore.no_simple_group_of_card_paqb
import Submission.Work.CharCore.Basic
import Submission.Work.NormalComplement.isIntegral_average_rootsOfUnity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace Work.NormalComplement

/-- From a `Multiset`-form representation of `z` as the average of `d` roots of unity, produce
the equivalent `Fin d`-indexed family.  Used to pass from the `Multiset` form of Huppert's
lemma to the `Fin`-indexed form `Work.NormalComplement.isIntegral_average_rootsOfUnity`. -/
theorem exists_fin_of_multiset_avg {z : ℂ} {d M : ℕ} (hd : 0 < d)
    (h : ∃ s : Multiset ℂ, s.card = d ∧ (∀ x ∈ s, x ^ M = 1) ∧ s.sum = (d : ℂ) * z) :
    ∃ ε : Fin d → ℂ, (∀ i, ε i ^ M = 1) ∧ (d : ℂ)⁻¹ * ∑ i, ε i = z := by
  obtain ⟨s, hcard, hroot, hsum⟩ := h
  have hl : s.toList.length = d := by rw [Multiset.length_toList, hcard]
  have hdl : d = s.toList.length := hl.symm
  refine ⟨fun i => s.toList.get (Fin.cast hdl i), ?_, ?_⟩
  · intro i
    exact hroot _ (Multiset.mem_toList.mp (List.get_mem _ _))
  · have h1 : ∑ i : Fin d, s.toList.get (Fin.cast hdl i)
        = ∑ i : Fin s.toList.length, s.toList.get i := by
      refine Fintype.sum_equiv (Fin.castOrderIso hdl).toEquiv _ _ ?_
      intro i
      rfl
    have h2 : ∑ i : Fin s.toList.length, s.toList.get i = s.toList.sum := by
      rw [← List.sum_ofFn, List.ofFn_get]
    have h3 : s.toList.sum = s.sum := by
      rw [← Multiset.sum_coe s.toList, Multiset.coe_toList]
    rw [h1, h2, h3, hsum, inv_mul_cancel_left₀ (by exact_mod_cast hd.ne')]

/-- **Huppert *Endliche Gruppen I* V.7.1**, `Multiset` form: an average of `d > 0` many `M`-th
roots of unity (`M > 0`) that is integral over `ℤ` is `0` or has modulus `1`.  Deduced from the
`Fin`-indexed form `Work.NormalComplement.isIntegral_average_rootsOfUnity` via
`exists_fin_of_multiset_avg`. -/
theorem avg_rootsOfUnity_multiset {z : ℂ} {d M : ℕ} (hd : 0 < d) (hM : 0 < M)
    (hint : IsIntegral ℤ z)
    (h : ∃ s : Multiset ℂ, s.card = d ∧ (∀ x ∈ s, x ^ M = 1) ∧ s.sum = (d : ℂ) * z) :
    z = 0 ∨ ‖z‖ = 1 := by
  obtain ⟨ε, hεM, hεz⟩ := exists_fin_of_multiset_avg hd h
  have hint' : IsIntegral ℤ ((d : ℂ)⁻¹ * ∑ i, ε i) := by rw [hεz]; exact hint
  rcases isIntegral_average_rootsOfUnity hd ε (fun i => ⟨M, hM, hεM i⟩) hint' with h0 | h1
  · exact Or.inl (by rw [← hεz, h0, mul_zero])
  · exact Or.inr (by rwa [hεz] at h1)

/-- **Burnside's result on classes of prime-power size** (Isaacs (3.9)) in the form the area needs
(`Work.NormalComplement.Design.BurnsideClassProp`, `_design/Vocab.lean`): a conjugacy class of
size `q ^ d > 1` is central modulo a proper normal subgroup.  The ingredients are already in
`Submission/Work/CharCore/` (`exists_irr_not_dvd_deg_char_ne_zero`,
`isIntegral_char_div_irrDeg`, `avg_rootsOfUnity_integral`, `norm_char_eq_iff_isScalar`,
`false_of_prime_pow_class_chi`): take `N = ker χ` for a non-linear `χ ∈ Irr W` with `q ∤ χ(1)` and
`χ x ≠ 0`, and drop the simplicity step of `false_of_prime_pow_class_chi`. -/
theorem burnsideClassProp : Work.NormalComplement.Design.BurnsideClassProp := by
  intro W _inst _fin x q d hq hd hclass
  classical
  haveI : Fintype W := Fintype.ofFinite W
  -- `x ≠ 1`, because a nontrivial class has at least two elements
  have hx : x ≠ 1 := by
    intro hx1
    have hcard1 : Nat.card (ConjClasses.mk (1 : W)).carrier = 1 := by
      rw [Work.CharCore.nat_card_conjClass_carrier_eq_index_centralizer]
      have hc : Subgroup.centralizer ({(1 : W)} : Set W) = ⊤ := by
        rw [Subgroup.eq_top_iff']
        intro g
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        simp
      rw [hc, Subgroup.index_top]
    rw [hx1, hcard1] at hclass
    have hgt : 1 < q ^ d := one_lt_pow₀ hq.one_lt (Nat.pos_iff_ne_zero.mp hd)
    omega
  obtain ⟨χ, hχ, hne, hqdvd, hval⟩ :=
    Work.CharCore.exists_irr_not_dvd_deg_char_ne_zero (G := W) hx hq
  refine ⟨Work.CharCore.irrKer χ hχ, Work.CharCore.irrKer_normal χ hχ, ?_, ?_⟩
  · -- the kernel of `χ` is a proper subgroup, since `χ` is not the principal character
    intro htop
    have hconst : ∀ g : W, χ g = (Work.CharCore.irrDeg χ : ℂ) := by
      intro g
      have h1 : g ∈ Work.CharCore.irrKer χ hχ := by rw [htop]; exact Subgroup.mem_top g
      rw [Work.CharCore.mem_irrKer hχ] at h1
      rw [← Work.CharCore.irrDeg_spec hχ]
      exact h1
    have h1 : Work.CharCore.cfInner χ (fun _ : W => (1 : ℂ)) = 0 := by
      rw [Work.CharCore.irr_orthonormal χ (fun _ : W => (1 : ℂ)) hχ
        Work.CharCore.principalChar_mem_Irr]
      simp [hne]
    have h2 : Work.CharCore.cfInner χ (fun _ : W => (1 : ℂ))
        = (Work.CharCore.irrDeg χ : ℂ) := by
      rw [Work.CharCore.cfInner_apply]
      simp only [map_one, mul_one]
      rw [Finset.sum_congr rfl (fun g _ => hconst g), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, inv_mul_cancel_left₀ (by exact_mod_cast Fintype.card_ne_zero)]
    rw [h1] at h2
    exact Work.CharCore.irrDeg_ne_zero hχ h2.symm
  · -- `⁅x, g⁆` lies in the kernel of `χ`
    intro g
    obtain ⟨N, hNmem, hNχ⟩ := Work.CharCore.exists_mem_irrSubmodules_of_mem_Irr hχ
    haveI hN : IsSimpleModule (Work.CharCore.groupAlgebra W) N :=
      Work.CharCore.isSimpleModule_of_mem_irrSubmodules N hNmem
    have hIrr : (Work.CharCore.submoduleRep N).IsIrreducible :=
      Work.CharCore.isIrreducible_submoduleRep N hN
    -- `χ x / χ 1` is an algebraic integer
    have hcop : Nat.Coprime (Nat.card (ConjClasses.mk x).carrier) (Work.CharCore.irrDeg χ) := by
      rw [hclass]
      exact (hq.coprime_iff_not_dvd.mpr hqdvd).pow_left d
    have hint : IsIntegral ℤ (χ x / (Work.CharCore.irrDeg χ : ℂ)) :=
      Work.CharCore.isIntegral_char_div_irrDeg hχ x hcop
    have hdeg : Module.finrank ℂ N = Work.CharCore.irrDeg χ :=
      (Work.CharCore.irrDeg_eq_finrank hχ hNmem hNχ).symm
    -- `χ x / χ 1` is the average of the eigenvalues of `ρ x`
    have hsplits : ((Work.CharCore.submoduleRep N) x).charpoly.Splits := IsAlgClosed.splits _
    have htr : (Work.CharCore.submoduleRep N).character x
        = ((Work.CharCore.submoduleRep N) x).charpoly.roots.sum :=
      Module.End.trace_eq_sum_roots_charpoly_of_splits hsplits
    have hroot : ∀ y ∈ ((Work.CharCore.submoduleRep N) x).charpoly.roots,
        y ^ orderOf x = 1 := by
      intro y hy
      have hev : Module.End.HasEigenvalue ((Work.CharCore.submoduleRep N) x) y :=
        (Module.End.hasEigenvalue_iff_isRoot_charpoly _ y).2 (Polynomial.isRoot_of_mem_roots hy)
      obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hev
      have hpowmap : ((Work.CharCore.submoduleRep N) x) ^ orderOf x = 1 := by
        rw [← map_pow, pow_orderOf_eq_one, map_one]
      have key : y ^ orderOf x • v = v := by
        rw [← Module.End.HasEigenvector.pow_apply hv (orderOf x), hpowmap, Module.End.one_apply]
      exact smul_left_injective ℂ hv.2 (by simpa using key)
    have hcard : ((Work.CharCore.submoduleRep N) x).charpoly.roots.card
        = Work.CharCore.irrDeg χ := by
      have h1 := hsplits.natDegree_eq_card_roots
      have h2 := LinearMap.charpoly_natDegree ((Work.CharCore.submoduleRep N) x)
      rw [← h1, h2]
      exact hdeg
    have hssum : ((Work.CharCore.submoduleRep N) x).charpoly.roots.sum
        = (Work.CharCore.irrDeg χ : ℂ) * (χ x / (Work.CharCore.irrDeg χ : ℂ)) := by
      rw [← htr, hNχ, mul_div_cancel₀ _ (Work.CharCore.irrDeg_ne_zero hχ)]
    have hL1 := avg_rootsOfUnity_multiset (Work.CharCore.irrDeg_pos hχ)
      (orderOf_pos x) hint
      ⟨((Work.CharCore.submoduleRep N) x).charpoly.roots, hcard, hroot, hssum⟩
    have hz0 : χ x / (Work.CharCore.irrDeg χ : ℂ) ≠ 0 :=
      div_ne_zero hval (Work.CharCore.irrDeg_ne_zero hχ)
    have hnorm1 : ‖χ x / (Work.CharCore.irrDeg χ : ℂ)‖ = 1 := hL1.resolve_left hz0
    have hnormχ : ‖χ x‖ = (Work.CharCore.irrDeg χ : ℝ) := by
      rw [norm_div, Complex.norm_natCast] at hnorm1
      rwa [div_eq_one_iff_eq (by exact_mod_cast (Work.CharCore.irrDeg_pos hχ).ne')] at hnorm1
    -- hence `ρ x` is a scalar matrix
    obtain ⟨c, _hc1, hcx⟩ :=
      (Work.CharCore.norm_char_eq_iff_isScalar (Work.CharCore.submoduleRep N) hIrr x).mp (by
        rw [hNχ]
        exact hnormχ)
    -- so `ρ x` commutes with every `ρ g`, and `ρ ⁅x,g⁆ = 1`
    have hcomm : ∀ y : W, (Work.CharCore.submoduleRep N) x * (Work.CharCore.submoduleRep N) y
        = (Work.CharCore.submoduleRep N) y * (Work.CharCore.submoduleRep N) x := by
      intro y
      rw [hcx, ← Algebra.algebraMap_eq_smul_one]
      exact (Algebra.commute_algebraMap_right c ((Work.CharCore.submoduleRep N) y)).eq.symm
    have hker : (Work.CharCore.submoduleRep N) (x * g * x⁻¹ * g⁻¹) = 1 := by
      have hconj : (Work.CharCore.submoduleRep N) (x * g * x⁻¹)
          = (Work.CharCore.submoduleRep N) g := by
        rw [map_mul, map_mul, hcomm g, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
      rw [show x * g * x⁻¹ * g⁻¹ = (x * g * x⁻¹) * g⁻¹ from by group, map_mul, hconj,
        ← map_mul, mul_inv_cancel, map_one]
    rw [Work.CharCore.mem_irrKer hχ, ← hNχ]
    simp only [Representation.character, hker, map_one]

end Work.NormalComplement
