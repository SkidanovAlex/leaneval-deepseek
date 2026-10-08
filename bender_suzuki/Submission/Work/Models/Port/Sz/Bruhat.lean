/-
The Bruhat decomposition `Sz(q) = B ∪ B w B` for the Suzuki group.

Let `B = U ⋊ T = szBorel n` and `w = szWg n` (the Weyl element).  The point of this
file is the *abstract* assembly of the Bruhat decomposition: assuming

* `w u w ∈ B ∪ B w B` for every root element `u = u(a,b) ∈ U`,

we prove that `B ∪ B w B` is a subgroup containing the generators `U`, `T`, `w`, hence
equals `SzModel n`, and deduce the order `|Sz(q)| = q^2(q-1)(q^2+1)`.

The single remaining matrix computation (`w u(a,b) w ∈ B ∪ B w B`) is delegated.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.Sz.Borel

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

open Matrix LeanEval.GroupTheory.Defs
open scoped Pointwise

namespace Submission.Sz

/-- The Borel subgroup as a set. -/
abbrev szBorelSet (n : ℕ) : Set (GL (Fin 4) (SzField n)) := ↑(szBorel n)

/-- The double coset `B w B`. -/
abbrev szBwB (n : ℕ) : Set (GL (Fin 4) (SzField n)) :=
  szBorelSet n * {szWg n} * szBorelSet n

/-- The set `B ∪ B w B` of the Bruhat decomposition. -/
def szBwBSet (n : ℕ) : Set (GL (Fin 4) (SzField n)) :=
  szBorelSet n ∪ szBwB n

lemma mem_szBwB (n : ℕ) (x : GL (Fin 4) (SzField n)) :
    x ∈ szBwB n ↔
      ∃ b₁ ∈ szBorel n, ∃ b₂ ∈ szBorel n, b₁ * szWg n * b₂ = x := by
  constructor
  · rintro ⟨y, ⟨b₁, h₁, b₁', hw, hy⟩, b₂, h₂, hxy⟩
    rw [Set.mem_singleton_iff] at hw
    subst hw
    refine ⟨b₁, h₁, b₂, h₂, ?_⟩
    rw [← hxy, ← hy]
  · rintro ⟨b₁, h₁, b₂, h₂, rfl⟩
    exact Set.mem_mul.mpr
      ⟨b₁ * szWg n, Set.mem_mul.mpr ⟨b₁, h₁, szWg n, Set.mem_singleton _, rfl⟩, b₂, h₂, rfl⟩

lemma szWg_mem_szBwB (n : ℕ) : szWg n ∈ szBwB n :=
  mem_szBwB n (szWg n) |>.mpr ⟨1, (szBorel n).one_mem, 1, (szBorel n).one_mem, by simp⟩

/-! ## Basic facts about the Weyl element -/

lemma szWg_mul_self (n : ℕ) : szWg n * szWg n = 1 := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_one, szWg_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [szW, Matrix.mul_apply, Fin.sum_univ_four]

lemma szWg_conj_mul (n : ℕ) (g h : GL (Fin 4) (SzField n)) :
    szWg n * (g * h) * szWg n = (szWg n * g * szWg n) * (szWg n * h * szWg n) := by
  have h1 : szWg n * (g * h) * szWg n =
      szWg n * g * (szWg n * szWg n) * h * szWg n := by
    rw [szWg_mul_self n]; group
  rw [h1]
  group

lemma szWg_conj_szTg (n : ℕ) (x : (SzField n)ˣ) :
    szWg n * szTg n x * szWg n = szTg n x⁻¹ := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_mul, szWg_coe, szTg_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [szW, szT, Matrix.mul_apply, Fin.sum_univ_four, Units.val_inv_eq_inv_val]

/-! ## The Bruhat set is closed under multiplication -/

lemma szBorelSet_mul_self (n : ℕ) : szBorelSet n * szBorelSet n = szBorelSet n := by
  simp [szBorelSet]

lemma szBorelSet_mul_szBwB (n : ℕ) : szBorelSet n * szBwB n = szBwB n := by
  simp only [szBwB]
  rw [← mul_assoc, ← mul_assoc, szBorelSet_mul_self]

lemma szBwB_mul_szBorelSet (n : ℕ) : szBwB n * szBorelSet n = szBwB n := by
  simp only [szBwB]
  rw [mul_assoc, szBorelSet_mul_self]

lemma szBorelSet_mul_szBwBSet (n : ℕ) : szBorelSet n * szBwBSet n ⊆ szBwBSet n := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hz
  rcases hy with hy | hy
  · exact Or.inl ((szBorel n).mul_mem hx hy)
  · exact Or.inr (by
      have h := Set.mul_mem_mul hx hy
      rwa [szBorelSet_mul_szBwB] at h)

lemma szBwBSet_mul_szBorelSet (n : ℕ) : szBwBSet n * szBorelSet n ⊆ szBwBSet n := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hz
  rcases hx with hx | hx
  · exact Or.inl ((szBorel n).mul_mem hx hy)
  · exact Or.inr (by
      have h := Set.mul_mem_mul hx hy
      rwa [szBwB_mul_szBorelSet] at h)

/-- The main structure theorem, conditional on the root-conjugation computation. -/
theorem szBwBSet_mul_mem (n : ℕ)
    (hwuw : ∀ a b : SzField n, szWg n * szUg n a b * szWg n ∈ szBwBSet n)
    {x y : GL (Fin 4) (SzField n)} (hx : x ∈ szBwBSet n) (hy : y ∈ szBwBSet n) :
    x * y ∈ szBwBSet n := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Or.inl ((szBorel n).mul_mem hx hy)
  · exact Or.inr (by
      have h := Set.mul_mem_mul hx hy
      rwa [szBorelSet_mul_szBwB] at h)
  · exact Or.inr (by
      have h := Set.mul_mem_mul hx hy
      rwa [szBwB_mul_szBorelSet] at h)
  · obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (mem_szBwB n x).mp hx
    obtain ⟨b₃, hb₃, b₄, hb₄, rfl⟩ := (mem_szBwB n y).mp hy
    have hmem : b₂ * b₃ ∈ (↑(szTwoGroup n) : Set (GL (Fin 4) (SzField n))) *
        ((szTgHom n).range : Set (GL (Fin 4) (SzField n))) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (szTwoGroup n) (szTgHom n).range
        (szTgHom_range_le_normalizer n)]
      exact (szBorel n).mul_mem hb₂ hb₃
    obtain ⟨u, hu, t, ht, hut⟩ := hmem
    obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨x, rfl⟩ := ht
    have hkey : b₁ * szWg n * (szUg n a b * szTg n x) * (szWg n * b₄) =
        b₁ * (szWg n * szUg n a b * szWg n) * (szTg n x⁻¹ * b₄) := by
      rw [show b₁ * szWg n * (szUg n a b * szTg n x) * (szWg n * b₄) =
            b₁ * (szWg n * (szUg n a b * szTg n x) * szWg n) * b₄ from by group,
          szWg_conj_mul n (szUg n a b) (szTg n x), szWg_conj_szTg n x]
      group
    have hgoal : b₁ * szWg n * b₂ * (b₃ * szWg n * b₄) =
        b₁ * (szWg n * szUg n a b * szWg n) * (szTg n x⁻¹ * b₄) := by
      rw [show b₁ * szWg n * b₂ * (b₃ * szWg n * b₄) =
            b₁ * szWg n * (b₂ * b₃) * (szWg n * b₄) from by group]
      rw [← hut]
      exact hkey
    rw [hgoal]
    refine szBwBSet_mul_szBorelSet n ?_
    refine Set.mul_mem_mul (szBorelSet_mul_szBwBSet n ?_) ?_
    · exact Set.mul_mem_mul hb₁ (hwuw a b)
    · exact (szBorel n).mul_mem (Subgroup.mem_sup_right ⟨x⁻¹, rfl⟩) hb₄

/-! ## The order of `SzModel n` -/

lemma szTg_inv (n : ℕ) (x : (SzField n)ˣ) : szTg n x⁻¹ = (szTg n x)⁻¹ :=
  map_inv (szTgHom n) x

lemma szWg_mul_szTg (n : ℕ) (x : (SzField n)ˣ) :
    szWg n * szTg n x = (szTg n x)⁻¹ * szWg n := by
  calc szWg n * szTg n x
      = szWg n * szTg n x * (szWg n * szWg n) := by rw [szWg_mul_self, mul_one]
    _ = (szWg n * szTg n x * szWg n) * szWg n := by group
    _ = (szTg n x)⁻¹ * szWg n := by rw [szWg_conj_szTg, szTg_inv]

lemma szUg_mul_szTg_apply_of_lt (n : ℕ) (a b : SzField n) (x : (SzField n)ˣ)
    {i j : Fin 4} (h : j < i) :
    ((szUg n a b * szTg n x : GL (Fin 4) (SzField n)) :
      Matrix (Fin 4) (Fin 4) (SzField n)) i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, szU, szT]

lemma szWg_conj_szUg_apply_of_gt (n : ℕ) (a b : SzField n) {i j : Fin 4} (h : i < j) :
    ((szWg n * szUg n a b * szWg n : GL (Fin 4) (SzField n)) :
      Matrix (Fin 4) (Fin 4) (SzField n)) i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, szU, szW]

lemma szWg_conj_szUg_apply_diag (n : ℕ) (a b : SzField n) (i : Fin 4) :
    ((szWg n * szUg n a b * szWg n : GL (Fin 4) (SzField n)) :
      Matrix (Fin 4) (Fin 4) (SzField n)) i i = 1 := by
  fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_four, szU, szW]

/-- `w` is not in the Borel subgroup (which consists of upper triangular matrices). -/
lemma szWg_notMem_szBorel (n : ℕ) : szWg n ∉ szBorel n := by
  intro h
  have hmem : szWg n ∈ (↑(szTwoGroup n) : Set (GL (Fin 4) (SzField n))) *
      ((szTgHom n).range : Set (GL (Fin 4) (SzField n))) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (szTwoGroup n) (szTgHom n).range
      (szTgHom_range_le_normalizer n)]
    exact h
  obtain ⟨u, hu, t, ht, hut⟩ := hmem
  obtain ⟨a, b, rfl⟩ := hu
  obtain ⟨x, rfl⟩ := ht
  have h2 : ((szWg n : GL (Fin 4) (SzField n)) : Matrix (Fin 4) (Fin 4) (SzField n)) 3 0 = 1 := by
    simp [szWg, szW]
  have h3 : ((szWg n : GL (Fin 4) (SzField n)) : Matrix (Fin 4) (Fin 4) (SzField n)) 3 0 = 0 := by
    rw [← hut]
    simp [Matrix.mul_apply, Fin.sum_univ_four, szU, szT, szTgHom_apply]
  rw [h3] at h2
  exact zero_ne_one h2

/-- The Borel subgroup and the opposite unipotent subgroup `w U w⁻¹` meet trivially. -/
lemma szBorel_inf_conj_szTwoGroup_eq_bot (n : ℕ) :
    szBorel n ⊓ (szTwoGroup n).map (MulAut.conj (szWg n)).toMonoidHom = ⊥ := by
  have hwinv : (szWg n)⁻¹ = szWg n := inv_eq_of_mul_eq_one_right (szWg_mul_self n)
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  obtain ⟨hAB, hAW⟩ := hA
  obtain ⟨u, hu, huA⟩ := hAW
  obtain ⟨a, b, rfl⟩ := hu
  have hAeq : A = szWg n * szUg n a b * szWg n := by
    rw [← huA]
    show szWg n * szUg n a b * (szWg n)⁻¹ = szWg n * szUg n a b * szWg n
    rw [hwinv]
  have hmem : A ∈ (↑(szTwoGroup n) : Set (GL (Fin 4) (SzField n))) *
      ((szTgHom n).range : Set (GL (Fin 4) (SzField n))) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (szTwoGroup n) (szTgHom n).range
      (szTgHom_range_le_normalizer n)]
    exact hAB
  obtain ⟨u', hu', t', ht', hut'⟩ := hmem
  obtain ⟨a', b', rfl⟩ := hu'
  obtain ⟨x', rfl⟩ := ht'
  simp only [szTgHom_apply] at hut'
  have hBrep : A = szUg n a' b' * szTg n x' := hut'.symm
  apply Units.ext
  ext i j
  rcases lt_trichotomy i j with h | h | h
  · rw [hAeq, szWg_conj_szUg_apply_of_gt n a b h]
    simp [Matrix.one_apply, ne_of_lt h]
  · subst h
    rw [hAeq, szWg_conj_szUg_apply_diag n a b i]
    simp [Matrix.one_apply]
  · rw [hBrep, szUg_mul_szTg_apply_of_lt n a' b' x' h]
    simp [Matrix.one_apply, (ne_of_lt h).symm]

/-- The double coset `B w B` equals `B w U`. -/
lemma szBwB_eq (n : ℕ) :
    szBwB n = szBorelSet n * {szWg n} * (szTwoGroup n : Set (GL (Fin 4) (SzField n))) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (mem_szBwB n y).mp hy
    have hmem : b₂ ∈ (↑(szTwoGroup n) : Set (GL (Fin 4) (SzField n))) *
        ((szTgHom n).range : Set (GL (Fin 4) (SzField n))) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (szTwoGroup n) (szTgHom n).range
        (szTgHom_range_le_normalizer n)]
      exact hb₂
    obtain ⟨u, hu, t, ht, hut⟩ := hmem
    obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨x, rfl⟩ := ht
    rw [← hut]
    simp only [szTgHom_apply]
    have hu'' : (szTg n x)⁻¹ * szUg n a b * szTg n x ∈ szTwoGroup n := by
      have hconj := szTg_conj_szUg n x⁻¹ a b
      simp only [szTg_inv, inv_inv] at hconj
      rw [hconj]
      exact ⟨_, _, rfl⟩
    have h1 : szUg n a b * szTg n x =
        szTg n x * ((szTg n x)⁻¹ * szUg n a b * szTg n x) := by group
    have heq : b₁ * szWg n * (szUg n a b * szTg n x) =
        (b₁ * (szTg n x)⁻¹) * szWg n * ((szTg n x)⁻¹ * szUg n a b * szTg n x) := by
      calc b₁ * szWg n * (szUg n a b * szTg n x)
          = b₁ * (szWg n * (szTg n x * ((szTg n x)⁻¹ * szUg n a b * szTg n x))) := by
            rw [h1]; group
        _ = b₁ * ((szWg n * szTg n x) * ((szTg n x)⁻¹ * szUg n a b * szTg n x)) := by group
        _ = b₁ * (((szTg n x)⁻¹ * szWg n) * ((szTg n x)⁻¹ * szUg n a b * szTg n x)) := by
            rw [szWg_mul_szTg]
        _ = (b₁ * (szTg n x)⁻¹) * szWg n * ((szTg n x)⁻¹ * szUg n a b * szTg n x) := by group
    rw [heq]
    refine Set.mul_mem_mul ?_ hu''
    have ht' : (szTg n x)⁻¹ ∈ (szTgHom n).range := ⟨x⁻¹, by rw [szTgHom_apply, szTg_inv]⟩
    exact Set.mul_mem_mul ((szBorel n).mul_mem hb₁ (Subgroup.mem_sup_right ht'))
      (Set.mem_singleton _)
  · intro y hy
    obtain ⟨x, hx, u, hu, rfl⟩ := Set.mem_mul.mp hy
    obtain ⟨b₁, hb₁, w, hw, rfl⟩ := Set.mem_mul.mp hx
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact (mem_szBwB n _).mpr ⟨b₁, hb₁, u, Subgroup.mem_sup_left hu, rfl⟩

/-- The Bruhat set is a subgroup. -/
noncomputable def szBwBSubgroup (n : ℕ)
    (hwuw : ∀ a b : SzField n, szWg n * szUg n a b * szWg n ∈ szBwBSet n) :
    Subgroup (GL (Fin 4) (SzField n)) where
  carrier := szBwBSet n
  one_mem' := Or.inl (szBorel n).one_mem
  mul_mem' := fun hx hy => szBwBSet_mul_mem n hwuw hx hy
  inv_mem' := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl ((szBorel n).inv_mem hx)
    · obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (mem_szBwB n x).mp hx
      have hwinv : (szWg n)⁻¹ = szWg n := inv_eq_of_mul_eq_one_right (szWg_mul_self n)
      refine Or.inr ((mem_szBwB n (b₁ * szWg n * b₂)⁻¹).mpr
        ⟨b₂⁻¹, (szBorel n).inv_mem hb₂, b₁⁻¹, (szBorel n).inv_mem hb₁, ?_⟩)
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, hwinv]
      group

theorem szModel_le_szBwBSubgroup (n : ℕ)
    (hwuw : ∀ a b : SzField n, szWg n * szUg n a b * szWg n ∈ szBwBSet n) :
    SzModel n ≤ szBwBSubgroup n hwuw := by
  rw [show SzModel n = Subgroup.closure {A : GL (Fin 4) (SzField n) |
      (A : Matrix (Fin 4) (Fin 4) (SzField n)) ∈ SzGenerators n} from rfl, Subgroup.closure_le]
  rintro A (⟨a, b, hab⟩ | ⟨x, hx⟩ | hw)
  · refine Or.inl ?_
    rw [show A = szUg n a b from Units.ext hab]
    exact Subgroup.mem_sup_left ⟨a, b, rfl⟩
  · refine Or.inl ?_
    rw [show A = szTg n x from Units.ext hx]
    exact Subgroup.mem_sup_right ⟨x, rfl⟩
  · refine Or.inr ?_
    rw [show A = szWg n from Units.ext hw]
    exact szWg_mem_szBwB n

theorem szBwBSubgroup_le_szModel (n : ℕ)
    (hwuw : ∀ a b : SzField n, szWg n * szUg n a b * szWg n ∈ szBwBSet n) :
    szBwBSubgroup n hwuw ≤ SzModel n := by
  intro x hx
  rcases hx with hx | hx
  · exact szBorel_le_szModel n hx
  · obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (mem_szBwB n x).mp hx
    exact (SzModel n).mul_mem ((SzModel n).mul_mem (szBorel_le_szModel n hb₁)
      (szWg_mem_szModel n)) (szBorel_le_szModel n hb₂)

/-- The Bruhat decomposition: `SzModel n = B ∪ B w B`. -/
theorem szModel_eq_szBwBSubgroup (n : ℕ)
    (hwuw : ∀ a b : SzField n, szWg n * szUg n a b * szWg n ∈ szBwBSet n) :
    SzModel n = szBwBSubgroup n hwuw :=
  le_antisymm (szModel_le_szBwBSubgroup n hwuw) (szBwBSubgroup_le_szModel n hwuw)

/-- `|Sz(q)| = q^2 (q - 1) (q^2 + 1)` where `q = 2^(2n+1)`. -/
theorem card_szModel (n : ℕ)
    (hwuw : ∀ a b : SzField n, szWg n * szUg n a b * szWg n ∈ szBwBSet n) :
    Nat.card (SzModel n) = Nat.card (SzField n) ^ 2 * (Nat.card (SzField n) - 1) *
      (Nat.card (SzField n) ^ 2 + 1) := by
  classical
  have heq : SzModel n = szBwBSubgroup n hwuw := szModel_eq_szBwBSubgroup n hwuw
  rw [heq]
  change Nat.card ↥(szBwBSet n) = Nat.card (SzField n) ^ 2 * (Nat.card (SzField n) - 1) *
      (Nat.card (SzField n) ^ 2 + 1)
  have hdisj : Disjoint (szBorelSet n) (szBwB n) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (mem_szBwB n x).mp hx'
    apply szWg_notMem_szBorel n
    have h2 : b₁⁻¹ * (b₁ * szWg n * b₂) * b₂⁻¹ ∈ szBorel n :=
      (szBorel n).mul_mem ((szBorel n).mul_mem ((szBorel n).inv_mem hb₁) hx)
        ((szBorel n).inv_mem hb₂)
    convert h2 using 1
    group
  have hcard1 : Nat.card ↥(szBwBSet n) = Nat.card ↥(szBorel n) + Nat.card ↥(szBwB n) := by
    have h := Nat.card_congr (Equiv.Set.union hdisj)
    rw [Nat.card_sum] at h
    simpa [szBwBSet] using h
  have hcard2 : Nat.card ↥(szBwB n) = Nat.card ↥(szBorel n) * Nat.card ↥(szTwoGroup n) := by
    have hbij : Function.Bijective
        (fun p : ↥(szBorel n) × ↥(szTwoGroup n) =>
          (⟨(p.1 : GL (Fin 4) (SzField n)) * szWg n * (p.2 : GL (Fin 4) (SzField n)),
            (mem_szBwB n _).mpr ⟨p.1, p.1.2, p.2, Subgroup.mem_sup_left p.2.2, rfl⟩⟩ :
              ↥(szBwB n))) := by
      constructor
      · rintro ⟨b₁, u₁⟩ ⟨b₂, u₂⟩ h
        have h' : (b₁ : GL (Fin 4) (SzField n)) * szWg n * (u₁ : GL (Fin 4) (SzField n)) =
            (b₂ : GL (Fin 4) (SzField n)) * szWg n * (u₂ : GL (Fin 4) (SzField n)) :=
          Subtype.ext_iff.mp h
        have hb : (b₂ : GL (Fin 4) (SzField n))⁻¹ * (b₁ : GL (Fin 4) (SzField n)) =
            szWg n * ((u₂ : GL (Fin 4) (SzField n)) * (u₁ : GL (Fin 4) (SzField n))⁻¹) *
              (szWg n)⁻¹ := by
          calc (b₂ : GL (Fin 4) (SzField n))⁻¹ * (b₁ : GL (Fin 4) (SzField n))
              = (b₂ : GL (Fin 4) (SzField n))⁻¹ *
                  ((b₁ : GL (Fin 4) (SzField n)) * szWg n * (u₁ : GL (Fin 4) (SzField n))) *
                  (u₁ : GL (Fin 4) (SzField n))⁻¹ * (szWg n)⁻¹ := by group
            _ = (b₂ : GL (Fin 4) (SzField n))⁻¹ *
                  ((b₂ : GL (Fin 4) (SzField n)) * szWg n * (u₂ : GL (Fin 4) (SzField n))) *
                  (u₁ : GL (Fin 4) (SzField n))⁻¹ * (szWg n)⁻¹ := by rw [h']
            _ = szWg n * ((u₂ : GL (Fin 4) (SzField n)) * (u₁ : GL (Fin 4) (SzField n))⁻¹) *
                  (szWg n)⁻¹ := by group
        have hmem : (b₂ : GL (Fin 4) (SzField n))⁻¹ * (b₁ : GL (Fin 4) (SzField n)) ∈
            szBorel n ⊓ (szTwoGroup n).map (MulAut.conj (szWg n)).toMonoidHom := by
          refine ⟨(szBorel n).mul_mem ((szBorel n).inv_mem b₂.2) b₁.2, ?_⟩
          exact Subgroup.mem_map.mpr ⟨(u₂ : GL (Fin 4) (SzField n)) *
            (u₁ : GL (Fin 4) (SzField n))⁻¹,
            (szTwoGroup n).mul_mem u₂.2 ((szTwoGroup n).inv_mem u₁.2), hb.symm⟩
        rw [szBorel_inf_conj_szTwoGroup_eq_bot] at hmem
        have hb_eq : (b₂ : GL (Fin 4) (SzField n))⁻¹ * (b₁ : GL (Fin 4) (SzField n)) = 1 :=
          Subgroup.mem_bot.mp hmem
        have hbGL : (b₁ : GL (Fin 4) (SzField n)) = (b₂ : GL (Fin 4) (SzField n)) :=
          (inv_mul_eq_one.mp hb_eq).symm
        have hb1 : b₁ = b₂ := Subtype.ext hbGL
        have hu1 : u₁ = u₂ := by
          apply Subtype.ext
          have h2 : szWg n * (u₁ : GL (Fin 4) (SzField n)) =
              szWg n * (u₂ : GL (Fin 4) (SzField n)) := by
            rw [hbGL] at h'
            refine mul_left_cancel (a := (b₂ : GL (Fin 4) (SzField n))) ?_
            rw [← mul_assoc, ← mul_assoc]
            exact h'
          exact mul_left_cancel h2
        exact Prod.ext hb1 hu1
      · intro y
        have hy : (y : GL (Fin 4) (SzField n)) ∈
            szBorelSet n * {szWg n} * (szTwoGroup n : Set (GL (Fin 4) (SzField n))) := by
          rw [← szBwB_eq]; exact y.2
        obtain ⟨x, hx, u, hu, hxu⟩ := Set.mem_mul.mp hy
        obtain ⟨b₁, hb₁, w, hw, hbw⟩ := Set.mem_mul.mp hx
        rw [Set.mem_singleton_iff] at hw
        subst hw
        refine ⟨(⟨b₁, hb₁⟩, ⟨u, hu⟩), Subtype.ext ?_⟩
        rw [← hxu, ← hbw]
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
    exact Nat.card_prod _ _
  rw [hcard1]
  rw [hcard2]
  rw [card_szBorel]
  rw [card_szTwoGroup]
  ring

end Submission.Sz
