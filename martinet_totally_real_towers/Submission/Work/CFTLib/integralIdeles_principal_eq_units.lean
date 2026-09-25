import Mathlib
import Submission.Work.CFTLib.NKIdeles

namespace Work.CFTLib

open NK.GlobalCFT

/-- An integral idèle whose idèle class is trivial is the principal idèle of a unit of the ring
of integers. -/
theorem integralIdeles_principal_eq_units {K : Type} [Field K] [NumberField K]
    (x : NK.GlobalCFT.Idele K) (hx : x ∈ NK.GlobalCFT.Idele.integralIdeles K)
    (h : NK.GlobalCFT.IdeleClassGroup.mk K x = 1) :
    ∃ u : (NumberField.RingOfIntegers K)ˣ,
      x = NK.GlobalCFT.Idele.principalIdele K
        (Units.map (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom u) := by
  -- The class of `x` is trivial, so `x` is a principal idèle `(k)`.
  have hx_mem : x ∈ Idele.principalSubgroup K :=
    (QuotientGroup.eq_one_iff x).mp (by rw [← IdeleClassGroup.mk_apply]; exact h)
  obtain ⟨k, hk⟩ := Idele.mem_principalSubgroup.mp hx_mem
  -- `hk : principalIdele K k = x`.
  rw [← hk] at hx
  -- Every finite `q`-adic valuation of `k` is trivial, because `(k)` is a local unit at `q`.
  have hval : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      q.valuation K (k : K) = 1 := by
    intro q
    have h1 := hx (Place.ofFinite q) (Place.isFinite_ofFinite q)
    rw [Idele.principalIdele_apply] at h1
    rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one] at h1
    rw [Units.coe_map] at h1
    rw [← Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq q (k : K)]
    exact h1
  -- Hence both `k` and `k⁻¹` are integral, and their product is `1`: `k` is a unit of `𝓞 K`.
  have hk_int : (k : K) ∈ (algebraMap (NumberField.RingOfIntegers K) K).range :=
    IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K (k : K)
      (fun q => (hval q).le)
  have hkinv_int : ((k⁻¹ : Kˣ) : K) ∈ (algebraMap (NumberField.RingOfIntegers K) K).range := by
    refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K
      ((k⁻¹ : Kˣ) : K) (fun q => ?_)
    have hq : q.valuation K ((k⁻¹ : Kˣ) : K) = 1 := by
      have h1 : ((k⁻¹ : Kˣ) : K) = (k : K)⁻¹ := by simp
      rw [h1, map_inv₀, hval q, inv_one]
    exact (hq).le
  obtain ⟨a, ha⟩ := hk_int
  obtain ⟨b, hb⟩ := hkinv_int
  -- `a * b = 1` and `b * a = 1` in `𝓞 K`.
  have hab : a * b = 1 := by
    refine NumberField.RingOfIntegers.ext ?_
    show algebraMap (NumberField.RingOfIntegers K) K (a * b) =
      algebraMap (NumberField.RingOfIntegers K) K 1
    rw [map_mul, map_one, ha, hb]
    simp
  have hba : b * a = 1 := by rw [mul_comm]; exact hab
  refine ⟨Units.mk a b hab hba, ?_⟩
  rw [← hk]
  congr 1
  refine Units.ext ?_
  rw [Units.coe_map, Units.val_mk]
  exact ha.symm

end Work.CFTLib
