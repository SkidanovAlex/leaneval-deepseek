import Mathlib

namespace Work.DSM2p

open ValuationSubring

/-- The ring hom `S →+* W` induced by `hW : W.toSubring = (algebraMap S L).range`,
i.e. by the fact that `W` is the image of `S` inside `L`. -/
noncomputable def imageHom {S L : Type*} [CommRing S] [Field L] [Algebra S L]
    (W : ValuationSubring L) (hW : W.toSubring = (algebraMap S L).range) : S →+* W :=
  (algebraMap S L).codRestrict W.toSubring (fun a => by
    rw [hW]; exact Set.mem_range_self a)

@[simp] theorem imageHom_coe {S L : Type*} [CommRing S] [Field L] [Algebra S L]
    (W : ValuationSubring L) (hW : W.toSubring = (algebraMap S L).range) (a : S) :
    ((imageHom W hW a : W) : L) = algebraMap S L a := rfl

theorem imageHom_surjective {S L : Type*} [CommRing S] [Field L] [Algebra S L]
    (W : ValuationSubring L) (hW : W.toSubring = (algebraMap S L).range) :
    Function.Surjective (imageHom W hW) := by
  intro w
  have hw : (w : L) ∈ (algebraMap S L).range := hW ▸ w.2
  obtain ⟨a, ha⟩ := hw
  exact ⟨a, Subtype.ext ha⟩

theorem imageHom_injective {S L : Type*} [CommRing S] [IsDomain S] [Field L]
    [Algebra S L] [IsFractionRing S L]
    (W : ValuationSubring L) (hW : W.toSubring = (algebraMap S L).range) :
    Function.Injective (imageHom W hW) := by
  intro a b hab
  exact IsFractionRing.injective S L (congrArg (fun x : W => (x : L)) hab)

theorem continuous_of_iInf_span_pow_eq_bot {S L : Type*} [CommRing S] [IsDomain S] [Field L]
    [Algebra S L] [IsFractionRing S L] (W : ValuationSubring L)
    (hW : W.toSubring = (algebraMap S L).range) (s : S)
    (hspans : (⨅ n : ℕ, Ideal.span {s ^ n}) = ⊥)
    (hlt : W.valuation (algebraMap S L s) < 1) :
    ∀ γ : W.ValueGroup, γ ≠ 0 → ∃ n : ℕ, W.valuation (algebraMap S L s) ^ n < γ := by
  intro γ hγ
  by_contra hcon
  push Not at hcon
  -- choose `y` with `v y = γ ≠ 0`
  obtain ⟨y, hy⟩ := W.valuation_surjective γ
  -- `v y = γ ≤ v s < 1`, so `y ∈ W`
  have hy_mem : y ∈ W := by
    rw [← W.valuation_le_one_iff]
    calc W.valuation y = γ := hy
      _ ≤ W.valuation (algebraMap S L s) ^ 1 := hcon 1
      _ = W.valuation (algebraMap S L s) := pow_one _
      _ ≤ 1 := le_of_lt hlt
  have hψinj : Function.Injective (imageHom W hW) := imageHom_injective W hW
  have hψsurj : Function.Surjective (imageHom W hW) := imageHom_surjective W hW
  let wy : W := ⟨y, hy_mem⟩
  obtain ⟨z, hz⟩ := hψsurj wy
  -- `z` lies in every ideal `(s^n)`
  have hzmem : z ∈ ⨅ n : ℕ, Ideal.span {s ^ n} := by
    rw [Ideal.mem_iInf]
    intro n
    -- `v y ≤ v(s)^n`, so `y` is divisible by `(imageHom s)^n` in `W`
    obtain ⟨c, hc⟩ : ∃ c : W, (c : L) * (algebraMap S L s) ^ n = y := by
      rw [← W.valuation_le_iff y ((algebraMap S L s) ^ n)]
      calc W.valuation y = γ := hy
        _ ≤ W.valuation (algebraMap S L s) ^ n := hcon n
        _ = W.valuation ((algebraMap S L s) ^ n) :=
              (map_pow W.valuation (algebraMap S L s) n).symm
    obtain ⟨u, hu⟩ := hψsurj c
    have hkey : imageHom W hW (u * s ^ n) = wy := by
      apply Subtype.ext
      show ((imageHom W hW (u * s ^ n) : W) : L) = ((wy : W) : L)
      rw [map_mul, map_pow, hu]
      push_cast
      rw [imageHom_coe, hc]
    have hzeq : z = u * s ^ n := hψinj (by rw [hz, hkey])
    rw [hzeq]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton (s ^ n)))
  have hz0 : z = 0 := by
    have : z ∈ (⊥ : Ideal S) := by rw [← hspans]; exact hzmem
    exact Ideal.mem_bot.mp this
  have hwy0 : wy = 0 := by rw [← hz, hz0, map_zero]
  have hy0 : y = 0 := congrArg (fun w : W => (w : L)) hwy0
  exact hγ (by rw [← hy, hy0, map_zero])

end Work.DSM2p
