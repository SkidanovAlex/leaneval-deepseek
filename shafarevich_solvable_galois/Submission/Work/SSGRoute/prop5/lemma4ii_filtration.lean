import Mathlib.GroupTheory.Nilpotent
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Submission.Work.SSGRoute.oneStep.magLead_pSeries_divisible
import Submission.Work.SSGRoute.prop5.adjacent.magnus_image_saturated
import Submission.Work.SSGRoute.prop5.pow_mem_pCentralSeries
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped commutatorElement
set_option maxHeartbeats 3200000

namespace Work.SSGRoute.prop5

variable {X : Type*}

/-! ## Elementary facts about the two filtrations

`P^i` denotes the paper's `i`-th term of the descending `p`-central series, i.e.
`Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1)`, and `γ_j` the paper's `j`-th term of the
descending central series, i.e. `(⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)`.
-/

/-- `powSubgroup 1 H = H`. -/
lemma powSubgroup_one {P : Type*} [Group P] (H : Subgroup P) :
    Work.Shrinking.powSubgroup 1 H = H := by
  refine le_antisymm (Work.Shrinking.powSubgroup_le 1 H) ?_
  intro x hx
  refine Subgroup.subset_closure ?_
  exact ⟨x, hx, by simp⟩

/-- `γ_k^{p^s} ⊆ P^{k+s}` (`Work.SSGRoute.prop5.pow_mem_pCentralSeries`). -/
lemma powSubgroup_lowerCentralSeries_le (p : ℕ) [Fact p.Prime] (X : Type) [Fintype X]
    (k s : ℕ) (hk : 1 ≤ k) :
    Work.Shrinking.powSubgroup (p ^ s)
        ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) ≤
      Work.Shrinking.pCentralSeries p (FreeGroup X) (k + s - 1) := by
  rw [Work.Shrinking.powSubgroup, Subgroup.closure_le]
  rintro z ⟨y, hy, rfl⟩
  exact Work.SSGRoute.prop5.pow_mem_pCentralSeries (P := FreeGroup X) p k s hk y (by simpa using hy)

/-- The right hand side of Lemma 4(ii) is contained in the left hand side: for `j ≤ k ≤ i` the
subgroup `γ_k^{p^{i-k}}` lies both in `γ_j` and in `P^i`. -/
theorem filtration_rhs_le (p : ℕ) [Fact p.Prime] (X : Type) [Fintype X] (i j : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i) :
    (⨆ k ∈ Finset.Icc j i, Work.Shrinking.powSubgroup (p ^ (i - k))
        ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)))
      ≤ Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1) ⊓
        (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) := by
  refine iSup_le fun k => iSup_le fun hk => le_inf ?_ ?_
  · obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    have hkpos : 1 ≤ k := le_trans hj hk1
    refine le_trans (powSubgroup_lowerCentralSeries_le p X k (i - k) hkpos) ?_
    rw [show k + (i - k) - 1 = i - 1 from by omega]
  · obtain ⟨hk1, _⟩ := Finset.mem_Icc.mp hk
    refine le_trans (Work.Shrinking.powSubgroup_le (p ^ (i - k)) _) ?_
    exact Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup (FreeGroup X)) (by omega)

/-- The family on the right hand side of Lemma 4(ii) is monotone in the lower index. -/
lemma rhs_mono (p : ℕ) (X : Type) [Group (FreeGroup X)] (i k : ℕ) :
    (⨆ t ∈ Finset.Icc (k + 1) i, Work.Shrinking.powSubgroup (p ^ (i - t))
        ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (t - 1)))
      ≤ ⨆ t ∈ Finset.Icc k i, Work.Shrinking.powSubgroup (p ^ (i - t))
        ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (t - 1)) := by
  refine iSup_le fun t => iSup_le fun ht => ?_
  refine le_iSup_of_le t (le_iSup_of_le ?_ le_rfl)
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ht
  exact Finset.mem_Icc.mpr ⟨by omega, h2⟩

/-! ## The hard direction of Lemma 4(ii)

Write `P^i := pCentralSeries p (FreeGroup X) (i-1)` and `γ_j := lowerCentralSeries (j-1)` (the
paper's indices).  The inclusion `P^i ∩ γ_j ≤ ⨆_{k∈[j,i]} γ_k^{p^{i-k}}` is proved from the single
"one-step" bound

  `P^i ∩ γ_j ≤ (γ_j)^{p^{i-j}} · γ_{j+1}`,       (`pSeries_inter_lcs_le_oneStep`)

which is Lemma 4(ii) of Schmidt–Wingberg with a single factor on the right, and which is the place
where the freeness of `FreeGroup X` enters (it is proved there via the Magnus embedding: the
leading term of an element of `P^i ∩ γ_j` is divisible by `p^{i-j}`, purity produces a `p^{i-j}`-th
root in `γ_j`, and the Magnus kernel detects `γ_{j+1}`).  Note that the bound is *false* for
arbitrary groups, e.g. for the modular group of order `16`, where `γ_2` is `2`-torsion.

From the one-step bound the full statement follows by descending induction on `j`: an element of
`P^i ∩ γ_j` splits as `x = u · v` with `u ∈ (γ_j)^{p^{i-j}}` and `v ∈ γ_{j+1}`; then
`v ∈ P^i ∩ γ_{j+1}` and the induction hypothesis applies to `v`, while `u` is the `k = j` term of
the right hand side. -/

/-- **The one-step bound** `P^i ∩ γ_j ≤ (γ_j)^{p^{i-j}} γ_{j+1}` (paper's indices); this is the
place where the freeness of `FreeGroup X` is used.

Let `x ∈ P^i ∩ γ_j`.  The leading term of the Magnus image of `x` is divisible by `p^{i-j}` inside
the degree-`j` part (`Work.SSGRoute.oneStep.magLead_pSeries_divisible`, the analytic input: an
element of `P^i` has Magnus weight `i`); by the purity (saturation) of the Magnus image
(`Work.SSGRoute.prop5.adjacent.magnus_image_saturated`) it is the leading term of an honest element
`w ∈ γ_j`.  Hence `z := x * w^{-p^{i-j}}` has vanishing leading term, so `z ∈ γ_{j+1}` by the Magnus
kernel (`Work.SSGRoute.prop5.mcore.magnusCore_aux`), and `x = z * w^{p^{i-j}}` lies in
`(γ_j)^{p^{i-j}} · γ_{j+1}`. -/
theorem pSeries_inter_lcs_le_oneStep (p : ℕ) [Fact p.Prime] (X : Type) (i j : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i) :
    Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1) ⊓
        (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) ≤
      Work.Shrinking.powSubgroup (p ^ (i - j))
          ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) ⊔
        (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := by
  intro x hx
  obtain ⟨hxP, hxγ⟩ := Subgroup.mem_inf.mp hx
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hn : 0 < p ^ (i - j) := pow_pos hp _
  -- the degree-`j` leading term of `x` is divisible by `p^(i-j)`
  obtain ⟨a, ha, haeq⟩ :=
    Work.SSGRoute.oneStep.magLead_pSeries_divisible p X i j hj hji hxP hxγ
  have haeq' : ((Work.SSGRoute.prop5.magnus X (j + 1) x :
        (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X (j + 1))ˣ) :
        Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X (j + 1)) - 1
      = ((p : ℤ) ^ (i - j)) • a := haeq
  -- purity: the quotient is the leading term of an element `w` of `γ_j`
  obtain ⟨w, hw, hweq⟩ := Work.SSGRoute.prop5.adjacent.magnus_image_saturated X
    (p ^ (i - j)) j hn hj x hxγ a ha (by rw [haeq', Nat.cast_pow, zsmul_eq_mul])
  have hweq' : Work.SSGRoute.prop5.magLead (j + 1) w = a := hweq
  set z : FreeGroup X := x * (w ^ (p ^ (i - j)))⁻¹ with hz
  have hwj : w ^ (p ^ (i - j)) ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) :=
    Subgroup.pow_mem _ hw _
  have hwinv : (w ^ (p ^ (i - j)))⁻¹ ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) :=
    Subgroup.inv_mem _ hwj
  have hxn : Work.SSGRoute.prop5.magLead (j + 1) x = ((p ^ (i - j) : ℕ) : ℤ) • a := by
    rw [haeq, Nat.cast_pow]
  have hwn : Work.SSGRoute.prop5.magLead (j + 1) (w ^ (p ^ (i - j)))
      = ((p ^ (i - j) : ℕ) : ℤ) • a := by
    rw [Work.SSGRoute.prop5.magLead_pow (j + 1) j (p ^ (i - j)) hj (by omega) (by omega) hw,
      hweq', zsmul_eq_mul]
  -- the difference has vanishing leading term, hence lies in `γ_{j+1}`
  have hzlt : Work.SSGRoute.prop5.magLead (j + 1) z = 0 := by
    rw [hz, Work.SSGRoute.prop5.magLead_mul (j + 1) j hj (by omega) (by omega) hxγ hwinv,
      Work.SSGRoute.prop5.magLead_inv (j + 1) j hj (by omega) (by omega) hwj, hwn, hxn]
    abel
  have hzmem : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := by
    refine Work.SSGRoute.prop5.mcore.mem_Gam_iff.mp
      (Work.SSGRoute.prop5.mcore.magnusCore_aux X j hj z
        (Work.SSGRoute.prop5.mcore.mem_Gam_iff.mpr ?_) hzlt)
    exact Subgroup.mul_mem _ hxγ hwinv
  have hdecomp : x = z * w ^ (p ^ (i - j)) := by rw [hz]; group
  rw [hdecomp]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hzmem)
    (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨w, hw, rfl⟩))

/-- **The adjacent case of Lemma 4(ii)**: `P^{j+1} ∩ γ_j ≤ γ_j^p γ_{j+1}`. -/
theorem pCentralSeries_succ_inter_lowerCentralSeries_le (p : ℕ) [Fact p.Prime] (X : Type) [Fintype X]
    (j : ℕ) (hj : 1 ≤ j) :
    Work.Shrinking.pCentralSeries p (FreeGroup X) j ⊓
        (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) ≤
      Work.Shrinking.powSubgroup p ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) ⊔
        (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := by
  have h := pSeries_inter_lcs_le_oneStep p X (j + 1) j hj (by omega)
  rwa [show j + 1 - 1 = j from by omega, show j + 1 - j = 1 from by omega, pow_one] at h

/-- The hard inclusion of Lemma 4(ii), by descending induction on the upper index `j`
(strong induction on `i - j`). -/
private theorem filtration_le_aux (p : ℕ) [Fact p.Prime] (X : Type) [Fintype X] :
    ∀ d i j : ℕ, i - j = d → 1 ≤ j → j ≤ i →
      Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1) ⊓
          (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) ≤
        ⨆ k ∈ Finset.Icc j i, Work.Shrinking.powSubgroup (p ^ (i - k))
            ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) := by
  intro d
  induction d with
  | zero =>
      rintro i j hid hj hji
      have hij : i = j := by omega
      refine le_trans ?_ (le_iSup_of_le j (le_iSup_of_le ?_ le_rfl))
      · show Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1) ⊓
            (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) ≤
          Work.Shrinking.powSubgroup (p ^ (i - j))
            ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1))
        rw [hij, Nat.sub_self, pow_zero, powSubgroup_one]
        exact inf_le_right
      · exact Finset.mem_Icc.mpr ⟨le_rfl, hji⟩
  | succ d ih =>
      rintro i j hid hj hji
      have hjlt : j < i := by omega
      have hstep := pSeries_inter_lcs_le_oneStep p X i j hj hji
      have hih : Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1) ⊓
          (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j ≤
          ⨆ k ∈ Finset.Icc (j + 1) i, Work.Shrinking.powSubgroup (p ^ (i - k))
            ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) :=
        ih i (j + 1) (by omega) (by omega) (by omega)
      -- `γ_j^{p^{i-j}}` is the `k = j` term of the right hand side and lies in `P^i`
      have hpowP : Work.Shrinking.powSubgroup (p ^ (i - j))
          ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) ≤
          Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1) := by
        refine le_trans (powSubgroup_lowerCentralSeries_le p X j (i - j) hj) ?_
        rw [show j + (i - j) - 1 = i - 1 from by omega]
      have hterm : Work.Shrinking.powSubgroup (p ^ (i - j))
          ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) ≤
          ⨆ k ∈ Finset.Icc j i, Work.Shrinking.powSubgroup (p ^ (i - k))
            ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) :=
        le_iSup_of_le j (le_iSup_of_le (Finset.mem_Icc.mpr ⟨le_rfl, hji⟩) le_rfl)
      intro x hx
      obtain ⟨hxP, hxG⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨u, hu, v, hv, huv⟩ := (Subgroup.mem_sup_of_normal_right
        (s := Work.Shrinking.powSubgroup (p ^ (i - j))
          ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)))
        (t := (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j)).mp
          (hstep (Subgroup.mem_inf.mpr ⟨hxP, hxG⟩))
      have hvP : v ∈ Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1) := by
        have h : v = u⁻¹ * x := by rw [← huv]; group
        rw [h]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hpowP hu)) hxP
      have hvR : v ∈ ⨆ k ∈ Finset.Icc j i, Work.Shrinking.powSubgroup (p ^ (i - k))
            ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) :=
        rhs_mono p X i j (hih (Subgroup.mem_inf.mpr ⟨hvP, hv⟩))
      have hxu : x = u * v := by rw [← huv]
      rw [hxu]
      exact Subgroup.mul_mem _ (hterm hu) hvR

/-- The main theorem of Lemma 4(ii).  The `⊆` direction is obtained from the one-step bound
`pSeries_inter_lcs_le_oneStep` by the descending induction `filtration_le_aux`; the `⊇` direction
is `filtration_rhs_le`. -/
theorem lemma4ii_filtration (p : ℕ) [Fact p.Prime] (X : Type) [Fintype X] (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) : Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1) ⊓ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) = ⨆ k ∈ Finset.Icc j i, Work.Shrinking.powSubgroup (p ^ (i - k)) ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) := by
  refine le_antisymm ?_ (filtration_rhs_le p X i j hj hji)
  exact filtration_le_aux p X (i - j) i j rfl hj hji

/-- Propagation of the adjacent case to all levels:
`γ_j^{p^m} ∩ (P^{j+m+1} γ_{j+1}) ≤ γ_j^{p^{m+1}} γ_{j+1}`.  It is the first factor of the
equality of Lemma 4(ii) at `(j+m+1, j)`: the `k = j` term of the right hand side is
`γ_j^{p^{m+1}}`, while every term with `k ≥ j+1` lies in `γ_{j+1}`. -/
theorem powSubgroup_inter_sup_le (p : ℕ) [Fact p.Prime] (X : Type) [Fintype X]
    (j m : ℕ) (hj : 1 ≤ j) :
    Work.Shrinking.powSubgroup (p ^ m)
          ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) ⊓
        (Work.Shrinking.pCentralSeries p (FreeGroup X) (j + m) ⊔
          (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j) ≤
      Work.Shrinking.powSubgroup (p ^ (m + 1))
          ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) ⊔
        (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := by
  intro x hx
  obtain ⟨hxA, hxP⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨y, hyP, z, hzγ, hyz⟩ := (Subgroup.mem_sup_of_normal_right
    (s := Work.Shrinking.pCentralSeries p (FreeGroup X) (j + m))
    (t := (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j)).mp hxP
  have hxle : x ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) :=
    Work.Shrinking.powSubgroup_le (p ^ m) _ hxA
  have hzle : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) :=
    Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup (FreeGroup X)) (by omega : j - 1 ≤ j) hzγ
  have hyle : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) := by
    have h : y = x * z⁻¹ := by rw [← hyz]; group
    rw [h]
    exact Subgroup.mul_mem _ hxle (Subgroup.inv_mem _ hzle)
  -- `y` lies in the full right hand side of Lemma 4(ii) at `(j+m+1, j)`
  have hyR : y ∈ ⨆ k ∈ Finset.Icc j (j + m + 1),
      Work.Shrinking.powSubgroup (p ^ (j + m + 1 - k))
        ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) := by
    rw [← lemma4ii_filtration p X (j + m + 1) j hj (by omega)]
    refine Subgroup.mem_inf.mpr ⟨?_, hyle⟩
    have hyP' : y ∈ Work.Shrinking.pCentralSeries p (FreeGroup X) (j + m + 1 - 1) := by
      rwa [show j + m + 1 - 1 = j + m from by omega]
    exact hyP'
  -- in that right hand side only the term `k = j` survives modulo `γ_{j+1}`
  have hle : (⨆ k ∈ Finset.Icc j (j + m + 1),
      Work.Shrinking.powSubgroup (p ^ (j + m + 1 - k))
        ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1))) ≤
      Work.Shrinking.powSubgroup (p ^ (m + 1))
          ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) ⊔
        (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := by
    refine iSup_le fun k => iSup_le fun hk => ?_
    obtain ⟨hk1, _⟩ := Finset.mem_Icc.mp hk
    rcases eq_or_lt_of_le hk1 with hkj | hklt
    · rw [hkj, show k + m + 1 - k = m + 1 from by omega]
      exact le_sup_left
    · refine le_trans (Work.Shrinking.powSubgroup_le (p ^ (j + m + 1 - k)) _) ?_
      refine le_trans (Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup (FreeGroup X))
        (by omega : j ≤ k - 1)) ?_
      exact le_sup_right
  have hyB : y ∈ Work.Shrinking.powSubgroup (p ^ (m + 1))
        ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) ⊔
        (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := hle hyR
  rw [← hyz]
  exact Subgroup.mul_mem _ hyB (Subgroup.mem_sup_right hzγ)

end Work.SSGRoute.prop5
