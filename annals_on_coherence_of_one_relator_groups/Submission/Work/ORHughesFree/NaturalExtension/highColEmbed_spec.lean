import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.TruncDefect

/-!
# The high-column embedding `highColEmbed k b i`

`highColEmbed k b i : Fin (k * min b i) → Fin (k * i)` sends the block/degree pair
`(q, s)` (with `q : Fin k`, `s : Fin (min b i)`) to the pair `(q, (i - min b i) + s)`, encoded
through `finProdFinEquiv`.  This module proves that it is injective and that its image is exactly
the set of `p : Fin (k * i)` whose degree satisfies `i ≤ b + p.modNat`.
-/

namespace Work.ORHughesFree.NaturalExtension

/-- The first (`Fin`-)coordinate of `finProdFinEquiv (a, b)` is `a`. -/
private lemma fpfe_divNat (m n : ℕ) (a : Fin m) (b : Fin n) :
    (finProdFinEquiv (a, b)).divNat = a := by
  have h := finProdFinEquiv_symm_apply (finProdFinEquiv (a, b))
  rw [Equiv.symm_apply_apply] at h
  exact (Prod.ext_iff.mp h.symm).1

/-- The second (`Fin`-)coordinate of `finProdFinEquiv (a, b)` is `b`. -/
private lemma fpfe_modNat (m n : ℕ) (a : Fin m) (b : Fin n) :
    (finProdFinEquiv (a, b)).modNat = b := by
  have h := finProdFinEquiv_symm_apply (finProdFinEquiv (a, b))
  rw [Equiv.symm_apply_apply] at h
  exact (Prod.ext_iff.mp h.symm).2

/-- `finProdFinEquiv` is inverse to splitting into `divNat`/`modNat`. -/
private lemma fpfe_divNat_modNat (m n : ℕ) (x : Fin (m * n)) :
    finProdFinEquiv (x.divNat, x.modNat) = x := by
  rw [← finProdFinEquiv_symm_apply x, Equiv.apply_symm_apply]

/-- Characterisation of the image of `finProdFinEquiv`, stated with the value of the second
coordinate so that no `Fin`-proof bookkeeping is needed. -/
private lemma fpfe_eq_iff {m n : ℕ} (a : Fin m) (b : Fin n) (y : Fin (m * n)) :
    finProdFinEquiv (a, b) = y ↔ a = y.divNat ∧ (b : ℕ) = (y.modNat : ℕ) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← h]; exact (fpfe_divNat m n a b).symm
    · rw [← h]; exact (congrArg Fin.val (fpfe_modNat m n a b)).symm
  · rintro ⟨h1, h2⟩
    have hb : b = y.modNat := Fin.ext h2
    rw [h1, hb]
    exact fpfe_divNat_modNat m n y

/-- The set of rescaled degrees `i - min b i + s` with `s < min b i` is exactly the set of
degrees `pn < i` with `i ≤ b + pn`. -/
private lemma exists_fin_min_iff (b i pn : ℕ) (hpn : pn < i) :
    (∃ s : Fin (min b i), i - min b i + (s : ℕ) = pn) ↔ i ≤ b + pn := by
  constructor
  · rintro ⟨s, hs⟩; omega
  · intro h
    have hle : i - min b i ≤ pn := by omega
    refine ⟨⟨pn - (i - min b i), by omega⟩, ?_⟩
    show i - min b i + (pn - (i - min b i)) = pn
    omega

theorem highColEmbed_spec (k b i : ℕ) :
    Function.Injective (highColEmbed k b i) ∧
      ∀ p : Fin (k * i), p ∈ Set.range (highColEmbed k b i) ↔ i ≤ b + (p.modNat : ℕ) := by
  refine ⟨?_, ?_⟩
  · intro l1 l2 h
    have hpair := finProdFinEquiv.injective h
    have hl1 : l1.divNat = l2.divNat := (Prod.ext_iff.mp hpair).1
    have hl2 : (⟨i - min b i + (l1.modNat : ℕ), by omega⟩ : Fin i)
        = (⟨i - min b i + (l2.modNat : ℕ), by omega⟩ : Fin i) := (Prod.ext_iff.mp hpair).2
    have hmod : l1.modNat = l2.modNat := by
      apply Fin.ext
      have h : i - min b i + (l1.modNat : ℕ) = i - min b i + (l2.modNat : ℕ) := by
        simpa using congrArg Fin.val hl2
      omega
    have e1 : finProdFinEquiv (l1.divNat, l1.modNat) = l1 := fpfe_divNat_modNat ..
    have e2 : finProdFinEquiv (l2.divNat, l2.modNat) = l2 := fpfe_divNat_modNat ..
    rw [← e1, ← e2, hl1, hmod]
  · intro p
    have hkey : p ∈ Set.range (highColEmbed k b i) ↔
        ∃ s : Fin (min b i), i - min b i + (s : ℕ) = (p.modNat : ℕ) := by
      constructor
      · rintro ⟨l, hl⟩
        obtain ⟨-, h2⟩ := (fpfe_eq_iff l.divNat _ p).mp hl
        exact ⟨l.modNat, h2⟩
      · rintro ⟨s, hs⟩
        refine ⟨finProdFinEquiv (p.divNat, s), ?_⟩
        refine (fpfe_eq_iff (finProdFinEquiv (p.divNat, s)).divNat _ p).mpr ⟨?_, ?_⟩
        · exact fpfe_divNat ..
        · show i - min b i + ((finProdFinEquiv (p.divNat, s)).modNat : ℕ) = (p.modNat : ℕ)
          rw [fpfe_modNat]
          exact hs
    rw [hkey]
    exact exists_fin_min_iff b i (p.modNat : ℕ) p.modNat.isLt

end Work.ORHughesFree.NaturalExtension
