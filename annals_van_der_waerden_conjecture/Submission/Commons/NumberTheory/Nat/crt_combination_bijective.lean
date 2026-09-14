import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.ZMod.Basic
import Submission.Commons.NumberTheory.Nat.prod_dvd_of_pairwise_coprime_dvd

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.Nat

open scoped BigOperators

theorem crt_combination_bijective (s : Finset ℕ) (hpos : ∀ m ∈ s, 0 < m)
    (hcop : ∀ m ∈ s, ∀ m' ∈ s, m ≠ m' → Nat.Coprime m m') :
    Function.Bijective (fun b : (∀ m : {m // m ∈ s}, ZMod (m : ℕ)) =>
      (∑ m : {m // m ∈ s}, (((b m).val : ℕ) : ZMod (∏ m ∈ s, m)) *
        (((∏ m ∈ s, m) / (m : ℕ) : ℕ) : ZMod (∏ m ∈ s, m)))) := by
  classical
  set M : ℕ := ∏ m ∈ s, m with hM
  haveI hNe : ∀ m : {m // m ∈ s}, NeZero (m : ℕ) :=
    fun m => ⟨ne_of_gt (hpos m m.property)⟩
  have hMpos : 0 < M := by
    rw [hM]
    exact Finset.prod_pos (fun m hm => hpos m hm)
  haveI hNeM : NeZero M := ⟨ne_of_gt hMpos⟩
  have hdvd : ∀ m : {m // m ∈ s}, (m : ℕ) ∣ M := by
    intro m
    rw [hM]
    exact Finset.dvd_prod_of_mem (fun x : ℕ => x) m.property
  have hMdiv : ∀ m : {m // m ∈ s}, M / (m : ℕ) = ∏ x ∈ s.erase (m : ℕ), x := by
    intro m
    have hp : 0 < (m : ℕ) := hpos m m.property
    have hprod := Finset.prod_erase_mul s (fun x : ℕ => x) m.property
    rw [hM, ← hprod]
    exact Nat.mul_div_cancel _ hp
  have hc : ∀ m : {m // m ∈ s}, Nat.Coprime (M / (m : ℕ)) (m : ℕ) := by
    intro m
    rw [hMdiv m]
    apply Nat.Coprime.prod_left
    intro p hp
    obtain ⟨hpm, hps⟩ := Finset.mem_erase.mp hp
    exact hcop p hps (m : ℕ) m.property hpm
  let f : (∀ m : {m // m ∈ s}, ZMod (m : ℕ)) → ZMod M :=
    fun b => ∑ m : {m // m ∈ s}, (((b m).val : ℕ) : ZMod M) *
        ((M / (m : ℕ) : ℕ) : ZMod M)
  change Function.Bijective f
  -- Key computation: the `m₀`-th residue of `f b`.
  have hcast : ∀ (b : ∀ m : {m // m ∈ s}, ZMod (m : ℕ)) (m₀ : {m // m ∈ s}),
      ZMod.castHom (hdvd m₀) (ZMod (m₀ : ℕ)) (f b) =
        b m₀ * ((M / (m₀ : ℕ) : ℕ) : ZMod (m₀ : ℕ)) := by
    intro b m₀
    have hterm : ∀ m : {m // m ∈ s},
        ZMod.castHom (hdvd m₀) (ZMod (m₀ : ℕ))
            ((((b m).val : ℕ) : ZMod M) * ((M / (m : ℕ) : ℕ) : ZMod M)) =
          (((b m).val : ℕ) : ZMod (m₀ : ℕ)) * ((M / (m : ℕ) : ℕ) : ZMod (m₀ : ℕ)) := by
      intro m
      rw [map_mul, map_natCast, map_natCast]
    simp only [f]
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun m _ => hterm m)]
    rw [Finset.sum_eq_single (s := Finset.univ) m₀]
    · rw [ZMod.natCast_zmod_val]
    · intro m _ hmne
      have h2 : ((M / (m : ℕ) : ℕ) : ZMod (m₀ : ℕ)) = 0 := by
        rw [ZMod.natCast_eq_zero_iff, hMdiv m]
        apply Finset.dvd_prod_of_mem (fun x : ℕ => x)
        rw [Finset.mem_erase]
        exact ⟨fun h => hmne (Subtype.ext h).symm, m₀.property⟩
      rw [h2, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ m₀) h
  refine ⟨?_, ?_⟩
  · intro b b' hbb'
    funext m₀
    have hb := hcast b m₀
    have hb' := hcast b' m₀
    rw [hbb'] at hb
    have heq : b m₀ * ((M / (m₀ : ℕ) : ℕ) : ZMod (m₀ : ℕ)) =
        b' m₀ * ((M / (m₀ : ℕ) : ℕ) : ZMod (m₀ : ℕ)) := by
      rw [← hb, hb']
    have hunit : IsUnit (((M / (m₀ : ℕ) : ℕ) : ZMod (m₀ : ℕ))) :=
      (ZMod.isUnit_iff_coprime _ _).mpr (hc m₀)
    exact (IsUnit.mul_left_inj hunit).mp heq
  · intro y
    let b : ∀ m : {m // m ∈ s}, ZMod (m : ℕ) :=
      fun m => ZMod.castHom (hdvd m) (ZMod (m : ℕ)) y *
        (((M / (m : ℕ) : ℕ) : ZMod (m : ℕ)))⁻¹
    refine ⟨b, ?_⟩
    have hbc : ∀ m₀ : {m // m ∈ s},
        b m₀ * ((M / (m₀ : ℕ) : ℕ) : ZMod (m₀ : ℕ)) =
          ZMod.castHom (hdvd m₀) (ZMod (m₀ : ℕ)) y := by
      intro m₀
      have hu : IsUnit (((M / (m₀ : ℕ) : ℕ) : ZMod (m₀ : ℕ))) :=
        (ZMod.isUnit_iff_coprime _ _).mpr (hc m₀)
      simp only [b]
      rw [mul_assoc, ZMod.inv_mul_of_unit _ hu, mul_one]
    have hcongr : ∀ m₀ : {m // m ∈ s},
        ZMod.castHom (hdvd m₀) (ZMod (m₀ : ℕ)) (f b) =
          ZMod.castHom (hdvd m₀) (ZMod (m₀ : ℕ)) y := by
      intro m₀
      rw [hcast b m₀, hbc m₀]
    have hz : f b - y = 0 := by
      have hval : (f b - y).val = 0 := by
        have hprod : (∏ m ∈ s, m) ∣ (f b - y).val := by
          apply prod_dvd_of_pairwise_coprime_dvd (t := s) hcop
          intro m hm
          have h : ZMod.castHom (hdvd ⟨m, hm⟩) (ZMod m) (f b - y) = 0 := by
            rw [map_sub, hcongr ⟨m, hm⟩, sub_self]
          rw [ZMod.castHom_apply, ZMod.cast_eq_val] at h
          exact (ZMod.natCast_eq_zero_iff (f b - y).val m).mp h
        have hdvdM : M ∣ (f b - y).val := hprod
        exact Nat.eq_zero_of_dvd_of_lt hdvdM (ZMod.val_lt (f b - y))
      exact (ZMod.val_eq_zero (f b - y)).mp hval
    exact sub_eq_zero.mp hz

end Commons.NumberTheory.Nat