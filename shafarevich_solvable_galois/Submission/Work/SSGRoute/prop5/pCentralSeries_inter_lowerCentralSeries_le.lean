import Mathlib
import Submission.Work.Shrinking.PCentral
import Submission.Work.ProP.lowerCentralSeries_le_pCentralSeries
import Submission.Work.SSGRoute.prop5.pow_mem_pCentralSeries
import Submission.Work.SSGRoute.prop5.mul_pow_mem_lowerCentralSeries
import Submission.Work.SSGRoute.prop5.commutator_lowerCentralSeries_le
import Submission.Work.SSGRoute.prop5.lemma4ii_filtration
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.prop5

open scoped commutatorElement

variable {X : Type}

/-! ## Elementary facts

For `j ≥ 1`, `G j` denotes the paper's `j`-th term of the descending central series,
`(⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)`, and `pFilt p i j` the right hand side
`⨆ k ∈ Icc j i, γ_k^{p^{i-k}}` of Lemma 4(ii) of Schmidt–Wingberg.
-/

/-- The paper's `j`-th lower central series term, i.e. `γ_j`. -/
abbrev G (X : Type) [Group (FreeGroup X)] (j : ℕ) : Subgroup (FreeGroup X) :=
  (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)

/-- `powSubgroup 1 H = H`. -/
lemma psubgroup_powSubgroup_one {P : Type*} [Group P] (H : Subgroup P) :
    Work.Shrinking.powSubgroup 1 H = H := by
  refine le_antisymm (Work.Shrinking.powSubgroup_le 1 H) ?_
  intro x hx
  exact Subgroup.subset_closure ⟨x, hx, by simp⟩

/-- The right hand side of Lemma 4(ii). -/
noncomputable def pFilt (p i j : ℕ) : Subgroup (FreeGroup X) :=
  ⨆ k ∈ Finset.Icc j i, Work.Shrinking.powSubgroup (p ^ (i - k)) (G X k)

@[simp] lemma pFilt_le_G (p i j : ℕ) : pFilt p i j (X := X) ≤ G X j := by
  refine iSup_le fun k => iSup_le fun hk => ?_
  obtain ⟨hk1, _⟩ := Finset.mem_Icc.mp hk
  exact le_trans (Work.Shrinking.powSubgroup_le (p ^ (i - k)) _)
    (Subgroup.lowerCentralSeries_antitone _ (by omega))

/-- `pFilt i i = γ_i`. -/
lemma pFilt_self (p i : ℕ) : pFilt p i i (X := X) = G X i := by
  rw [pFilt]
  simp [psubgroup_powSubgroup_one]

/-- `pFilt` is monotone in the lower index. -/
lemma pFilt_mono_right (p i j : ℕ) : pFilt p i (j + 1) (X := X) ≤ pFilt p i j := by
  refine iSup_le fun k => iSup_le fun hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
  exact le_iSup_of_le k (le_iSup_of_le (Finset.mem_Icc.mpr ⟨by omega, hk2⟩) le_rfl)

/-- Splitting off the `k = j` term (for `j < i`). -/
lemma pFilt_succ (p i j : ℕ) (h : j + 1 ≤ i) :
    pFilt p i j (X := X) =
      Work.Shrinking.powSubgroup (p ^ (i - j)) (G X j) ⊔ pFilt p i (j + 1) := by
  apply le_antisymm
  · refine iSup_le fun k => iSup_le fun hk => ?_
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    rcases eq_or_lt_of_le hk1 with hkj | hklt
    · subst hkj; exact le_sup_left
    · refine le_sup_right.trans' ?_
      exact le_iSup_of_le k (le_iSup_of_le (Finset.mem_Icc.mpr ⟨by omega, hk2⟩) le_rfl)
  · refine sup_le ?_ (pFilt_mono_right p i j)
    exact le_iSup_of_le j (le_iSup_of_le (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) le_rfl)

/-- Each `pFilt` term is normal (a finite supremum of normal subgroups). -/
lemma pFilt_normal (p i j : ℕ) : (pFilt p i j (X := X)).Normal := by
  classical
  rw [pFilt]
  generalize h : Finset.Icc j i = s
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.iSup_insert]
      haveI : (Work.Shrinking.powSubgroup (p ^ (i - a)) (G X a)).Normal :=
        Work.Shrinking.powSubgroup_normal _ _
      exact Subgroup.sup_normal _ _

/-- `γ_k^{p^s} ≤ pCentralSeries p _ (k + s - 1)`. -/
lemma powSubgroup_G_le_pSeries (p : ℕ) [Fact p.Prime] (k s : ℕ) (hk : 1 ≤ k) :
    Work.Shrinking.powSubgroup (p ^ s)
        ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) ≤
      Work.Shrinking.pCentralSeries p (FreeGroup X) (k + s - 1) := by
  rw [Work.Shrinking.powSubgroup, Subgroup.closure_le]
  rintro z ⟨y, hy, rfl⟩
  exact pow_mem_pCentralSeries (P := FreeGroup X) p k s hk y hy

/-- `pFilt p i j ≤ pCentralSeries p _ (i-1)` for `1 ≤ j` (the `⊇` half of Lemma 4(ii)). -/
lemma pFilt_le_pSeries (p : ℕ) [Fact p.Prime] (i j : ℕ) (hj : 1 ≤ j) :
    pFilt p i j (X := X) ≤ Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1) := by
  refine iSup_le fun k => iSup_le fun hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
  refine le_trans (powSubgroup_G_le_pSeries (X := X) p k (i - k) (le_trans hj hk1)) ?_
  rw [show k + (i - k) - 1 = i - 1 from by omega]

/-! ## The induction

The `⊆` direction of Lemma 4(ii) is proved from two ingredients, both consequences of the freeness
of `FreeGroup X` (the statement is false for general groups, e.g. for the modular group of order
`16`), established in `lemma4ii_filtration`:

* the adjacent case `P^{j+1} ∩ γ_j ≤ γ_j^p γ_{j+1}` (`pCentralSeries_succ_inter_lowerCentralSeries_le`);
* its propagation `γ_j^{p^m} ∩ (P^{j+m+1} γ_{j+1}) ≤ γ_j^{p^{m+1}} γ_{j+1}` (`powSubgroup_inter_sup_le`).

The induction is on `i` and, for fixed `i`, descending on `j`.  For `x ∈ P^i ∩ γ_j` with
`j + 1 < i` one uses the induction hypothesis at `(i-1, j)`: `x = x₁ x₂` with
`x₁ ∈ γ_j^{p^{i-1-j}}` and `x₂ ∈ γ_{j+1}`.  Then `x₁ = x x₂⁻¹ ∈ P^i γ_{j+1}`, so the propagation
at `(j, i-1-j)` (whose `p`-central index is exactly `i`) shows `x₁ = u v` with
`u ∈ γ_j^{p^{i-j}}` and `v ∈ γ_{j+1}`; the remainder `v x₂ = x u⁻¹` still lies in `P^i ∩ γ_{j+1}`
and is handled by the induction hypothesis at `(i, j+1)`.
-/

/-- The main theorem: the `⊆` direction of Lemma 4(ii) of Schmidt–Wingberg. -/
theorem pCentralSeries_inter_lowerCentralSeries_le (p : ℕ) [Fact p.Prime] (X : Type) [Fintype X]
    (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) :
    Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1) ⊓
        (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) ≤
      ⨆ k ∈ Finset.Icc j i, Work.Shrinking.powSubgroup (p ^ (i - k))
          ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) := by
  classical
  -- `γ_j^{p^{i-j}} ⊆ pFilt p i j`
  have hmem_pow : ∀ i j : ℕ, 1 ≤ j → j ≤ i →
      Work.Shrinking.powSubgroup (p ^ (i - j)) (G X j) ≤ pFilt p i j := by
    intro i j hj hle
    exact le_iSup_of_le j (le_iSup_of_le (Finset.mem_Icc.mpr ⟨le_rfl, hle⟩) le_rfl)
  -- `γ_j^{p^{i-j}} ⊆ P^i` (via `γ_j^{p^s} ⊆ P^{j+s}`)
  have hpow_le_P : ∀ i j : ℕ, 1 ≤ j → j ≤ i →
      Work.Shrinking.powSubgroup (p ^ (i - j)) (G X j) ≤
        Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1) := by
    intro i j hj hle
    refine le_trans (powSubgroup_G_le_pSeries (X := X) p j (i - j) hj) ?_
    rw [show j + (i - j) - 1 = i - 1 from by omega]
  have hmain : ∀ d i j : ℕ, i - j = d → 1 ≤ j → j ≤ i →
      Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1) ⊓ G X j ≤ pFilt p i j := by
    intro d
    induction d with
    | zero =>
        intro i j hd hj hji
        have hij : i = j := by omega
        subst hij
        rw [pFilt_self]
        exact le_of_eq (le_antisymm inf_le_right
          (le_inf (Work.ProP.lowerCentralSeries_le_pCentralSeries p (FreeGroup X) (i - 1)) le_rfl))
    | succ d ihd =>
        intro i j hd hj hji
        have hjlt : j < i := by omega
        rcases eq_or_lt_of_le (show j + 1 ≤ i from hjlt) with h | h
        · -- `i = j + 1`: the adjacent case
          have hi : i = j + 1 := h.symm
          subst hi
          rw [pFilt_succ (p := p) (i := j + 1) (j := j) (by omega),
            pFilt_self (p := p) (i := j + 1),
            show j + 1 - j = 1 from by omega, pow_one,
            show j + 1 - 1 = j from by omega]
          exact pCentralSeries_succ_inter_lowerCentralSeries_le p X j hj
        · -- `j + 1 < i`
          have hprev := ihd (i - 1) j (by omega) hj (by omega)
          have hnext := ihd i (j + 1) (by omega) (by omega) (by omega)
          intro x hx
          obtain ⟨hxP, hxG⟩ := Subgroup.mem_inf.mp hx
          -- `x ∈ P^{i-1}`
          have hxP' : x ∈ Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1 - 1) := by
            refine Work.Shrinking.pCentralSeries_le_succ p (FreeGroup X) (i - 1 - 1) ?_
            rwa [show i - 1 - 1 + 1 = i - 1 from by omega]
          -- the induction hypothesis at `(i-1, j)`
          have hxmem : x ∈ pFilt p (i - 1) j := hprev (Subgroup.mem_inf.mpr ⟨hxP', hxG⟩)
          rw [pFilt_succ (p := p) (i := i - 1) (j := j) (by omega)] at hxmem
          haveI : (pFilt p (i - 1) (j + 1) (X := X)).Normal := pFilt_normal p (i - 1) (j + 1)
          obtain ⟨x1, hx1, x2, hx2, hx12⟩ :=
            (Subgroup.mem_sup_of_normal_right
              (s := Work.Shrinking.powSubgroup (p ^ (i - 1 - j)) (G X j))
              (t := pFilt p (i - 1) (j + 1))).mp hxmem
          -- `x1 = x * x2⁻¹ ∈ P^i ⊔ γ_{j+1}`
          have hx2G : x2 ∈ G X (j + 1) := pFilt_le_G p (i - 1) (j + 1) hx2
          have hx1sup : x1 ∈ Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1) ⊔ G X (j + 1) := by
            haveI : (Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1)).Normal :=
              Work.Shrinking.pCentralSeries_normal p (FreeGroup X) (i - 1)
            refine (Subgroup.mem_sup_of_normal_left
              (s := Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1))
              (t := G X (j + 1))).mpr ⟨x, hxP, x2⁻¹, Subgroup.inv_mem _ hx2G, ?_⟩
            rw [← hx12]
            group
          -- the propagation at `(j, i-1-j)`: its `p`-central index is `j + (i-1-j) = i-1`
          have hprop := powSubgroup_inter_sup_le p X j (i - 1 - j) hj
          rw [show j + (i - 1 - j) = i - 1 from by omega,
            show i - 1 - j + 1 = i - j from by omega] at hprop
          obtain ⟨u, hu, v, hv, huv⟩ :=
            (Subgroup.mem_sup_of_normal_right
              (s := Work.Shrinking.powSubgroup (p ^ (i - j)) (G X j))
              (t := G X (j + 1))).mp (hprop (Subgroup.mem_inf.mpr ⟨hx1, hx1sup⟩))
          -- the remainder `r = v * x2 = x * u⁻¹` lies in `P^i ∩ γ_{j+1}`
          have hr : (v * x2) ∈
              Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1) ⊓ G X (j + 1) := by
            refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mul_mem _ hv hx2G⟩
            have heq : v * x2 = u⁻¹ * x := by rw [← hx12, ← huv]; group
            rw [heq]
            exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hpow_le_P i j hj hji hu)) hxP
          -- and it is handled by the induction hypothesis at `(i, j+1)`
          have hr' : (v * x2) ∈ pFilt p i (j + 1) := hnext hr
          have hxu : x = u * (v * x2) := by rw [← hx12, ← huv]; group
          rw [hxu]
          exact Subgroup.mul_mem _ (hmem_pow i j hj hji hu) (pFilt_mono_right p i j hr')
  exact hmain (i - j) i j rfl hj hji

end Work.SSGRoute.prop5
