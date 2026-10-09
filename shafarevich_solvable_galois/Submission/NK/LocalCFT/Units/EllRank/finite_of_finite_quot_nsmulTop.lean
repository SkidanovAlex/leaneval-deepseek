import Mathlib
import Submission.NK.LocalCFT.Units.EllRank.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalCFT.Units.EllRank

/-- The subgroup `p ^ k • A` of `k`-fold `p`-multiples of an additive commutative group. -/
private def powSub (A : Type*) [AddCommGroup A] (p k : ℕ) : AddSubgroup A :=
  (⊤ : AddSubgroup A).map (nsmulAddMonoidHom (p ^ k))

private lemma mem_powSub {A : Type*} [AddCommGroup A] (p k : ℕ) (x : A) :
    x ∈ powSub A p k ↔ ∃ y : A, (p ^ k) • y = x := by
  rw [powSub, AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, -, hy⟩
    exact ⟨y, by rwa [nsmulAddMonoidHom_apply] at hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, trivial, by rwa [nsmulAddMonoidHom_apply]⟩

private lemma powSub_zero {A : Type*} [AddCommGroup A] (p : ℕ) : powSub A p 0 = ⊤ := by
  ext x; simp [powSub]

private lemma powSub_one {A : Type*} [AddCommGroup A] (p : ℕ) :
    powSub A p 1 = nsmulTop p A := by
  simp [powSub, nsmulTop]

/-- If `A` is annihilated by `p ^ e` and the quotient `A ⧸ pA` is finite, then `A` is finite.

Indeed, choosing a set of coset representatives for `A ⧸ pA`, the identity `A = N + pA`
for their span `N` iterates to `A = N + p ^ k A` for every `k`; at `k = e` the second
term vanishes, so `A` is finitely generated over `ℤ`, and a finitely generated torsion
abelian group is finite. -/
theorem finite_of_finite_quot_nsmulTop {A : Type*} [AddCommGroup A] {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hexp : ∀ x : A, (p ^ e) • x = 0) (hfin : Finite (A ⧸ nsmulTop p A)) : Finite A := by
  have _ : 1 ≤ e := he
  -- a section of the quotient map `A → A ⧸ pA`
  let sec : (A ⧸ nsmulTop p A) → A :=
    fun b => Classical.choose (QuotientAddGroup.mk_surjective b)
  have hsec : ∀ b, (QuotientAddGroup.mk (sec b) : A ⧸ nsmulTop p A) = b :=
    fun b => Classical.choose_spec (QuotientAddGroup.mk_surjective b)
  let N : AddSubgroup A := AddSubgroup.closure (Set.range sec)
  have hsecN : ∀ b, sec b ∈ N := fun b => AddSubgroup.subset_closure ⟨b, rfl⟩
  -- `A = N + pA`
  have h1 : (⊤ : AddSubgroup A) ≤ N ⊔ powSub A p 1 := by
    rw [powSub_one]
    intro x _
    have hxH : x - sec (QuotientAddGroup.mk x) ∈ nsmulTop p A :=
      QuotientAddGroup.eq_iff_sub_mem.mp (hsec (QuotientAddGroup.mk x)).symm
    exact AddSubgroup.mem_sup.mpr
      ⟨sec (QuotientAddGroup.mk x), hsecN _,
       x - sec (QuotientAddGroup.mk x), hxH, by abel⟩
  -- `p ^ k A ≤ N + p ^ (k+1) A`
  have hCk : ∀ k, powSub A p k ≤ N ⊔ powSub A p (k + 1) := by
    intro k y hy
    rw [mem_powSub] at hy
    obtain ⟨z, hz⟩ := hy
    rw [← hz]
    have hz1 : z ∈ N ⊔ powSub A p 1 := h1 (AddSubgroup.mem_top z)
    rw [AddSubgroup.mem_sup] at hz1
    obtain ⟨n, hn, c, hc, rfl⟩ := hz1
    refine AddSubgroup.mem_sup.mpr
      ⟨(p ^ k) • n, AddSubgroup.nsmul_mem N hn (p ^ k), (p ^ k) • c, ?_,
        (nsmul_add n c (p ^ k)).symm⟩
    rw [mem_powSub] at hc ⊢
    obtain ⟨w, hw⟩ := hc
    refine ⟨w, ?_⟩
    have hpk : p ^ (k + 1) = p ^ k * p ^ 1 := by rw [pow_one, pow_succ]
    rw [← hw, ← mul_smul, hpk]
  -- `N + p ^ k A` is increasing in `k`
  have hstep : ∀ k, N ⊔ powSub A p k ≤ N ⊔ powSub A p (k + 1) := fun k =>
    le_trans (sup_le_sup_left (hCk k) N) (le_of_eq (by rw [← sup_assoc, sup_idem]))
  have hkey : ∀ k, (⊤ : AddSubgroup A) ≤ N ⊔ powSub A p k := by
    intro k
    induction k with
    | zero => rw [powSub_zero]; exact le_sup_right
    | succ k ih => exact le_trans ih (hstep k)
  -- `p ^ e A = 0`
  have hCe : powSub A p e ≤ ⊥ := by
    intro x hx
    rw [mem_powSub] at hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy, hexp y]
    exact AddSubgroup.zero_mem ⊥
  have hNtop : N = ⊤ := top_le_iff.mp (le_trans (hkey e) (sup_le le_rfl (hCe.trans bot_le)))
  -- so `A` is finitely generated, and torsion, hence finite
  have hfinr : (Set.range sec).Finite := @Set.finite_range A (A ⧸ nsmulTop p A) sec hfin
  have hfg : AddGroup.FG A := AddGroup.fg_iff.mpr ⟨Set.range sec, hNtop, hfinr⟩
  have htor : IsAddTorsion A :=
    fun x => isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨p ^ e, pow_pos hp.pos e, hexp x⟩
  exact @AddCommGroup.finite_of_fg_isAddTorsion A _ hfg htor

end NK.LocalCFT.Units.EllRank
