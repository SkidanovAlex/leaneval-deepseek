import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmF.ChV12.chi_on_D

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `K̄ = ⟨K⟩` is normal in `D = H ∩ H^t`

Peterfalvi II, Ch. V §1 Prop. 2: in the split rank-one situation, with
`D = twoPoint H t = H ∩ Hᵗ`, `K = J(D,t) = Kset H t = {x ∈ D | t x t⁻¹ = x⁻¹}` and
`K̄ = ⟨K⟩ = Ksub H t`, the set `K` is a subgroup of `D` (this is the hypothesis `hKset`,
the content of Prop. 2), and hence `K̄ ⊴ D`.

The argument, purely group-theoretic, is short.  Since `K̄` has carrier `K`:

* every element of `K̄` is inverted by `t` (directly from `K̄ = K`);
* consequently `K̄` is **abelian**: for `a b ∈ K̄` also `a b ∈ K̄`, so
  `a⁻¹ b⁻¹ = t(ab)t⁻¹ = (ab)⁻¹ = b⁻¹ a⁻¹`;
* for `d ∈ D` and `k ∈ K̄`, the element `g := d⁻¹ (t d t⁻¹)` lies in `K̄`
  (it lies in `D` and is inverted by `t`), and `k⁻¹ ∈ K̄`; abelianness gives
  `g k⁻¹ g⁻¹ = k⁻¹`, which rearranges to `t (d k d⁻¹) t⁻¹ = (d k d⁻¹)⁻¹`,
  i.e. `d k d⁻¹ ∈ K̄`.  Hence `D ≤ N_G(K̄)` and `K̄ ⊴ D`.

The `t`-conjugation computations are carried out with `MulAut.conj t` and `t² = 1`.
-/

namespace Work.ThmF.ChV12

theorem KsubSubgroupOfNormal {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hKset : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t) :
    ((Work.ThmF.Ksub H t).subgroupOf (Submission.Blueprint.twoPoint H t)).Normal := by
  -- `K̄` has carrier `K = Kset H t`
  have hKm : ∀ x : G, x ∈ Work.ThmF.Ksub H t ↔ x ∈ Work.ThmF.Kset H t := fun x => by
    show x ∈ (Work.ThmF.Ksub H t : Set G) ↔ x ∈ Work.ThmF.Kset H t
    rw [hKset]
  have hle : Work.ThmF.Ksub H t ≤ Submission.Blueprint.twoPoint H t :=
    Work.ThmF.Ksub_le_twoPoint t
  -- `t` is an involution
  have ht2 : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [h.invol] at h1
    simpa [pow_two] using h1
  -- `t` normalises `D`
  have htnorm : t ∈ Subgroup.normalizer ((Submission.Blueprint.twoPoint H t : Subgroup G) : Set G) :=
    Work.ThmF.normalizes_twoPoint_of_data (Work.ThmF.IsSplitRankOne.toData h)
  have htmem : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      t * d * t⁻¹ ∈ Submission.Blueprint.twoPoint H t :=
    fun d hd => (Subgroup.mem_normalizer_iff.mp htnorm d).mp hd
  -- `K̄` is abelian
  have hab : ∀ a ∈ Work.ThmF.Ksub H t, ∀ b ∈ Work.ThmF.Ksub H t, a * b = b * a := by
    intro a ha b hb
    have ha' : t * a * t⁻¹ = a⁻¹ := ((hKm a).mp ha).2
    have hb' : t * b * t⁻¹ = b⁻¹ := ((hKm b).mp hb).2
    have hab' : t * (a * b) * t⁻¹ = (a * b)⁻¹ :=
      ((hKm (a * b)).mp ((Work.ThmF.Ksub H t).mul_mem ha hb)).2
    have e1 : t * (a * b) * t⁻¹ = a⁻¹ * b⁻¹ := by
      rw [show t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) by group, ha', hb']
    rw [e1, mul_inv_rev] at hab'
    have h2 := congrArg (fun z : G => z⁻¹) hab'
    simp only [mul_inv_rev, inv_inv] at h2
    exact h2.symm
  -- the key: `D` normalises `K̄`
  have key : ∀ d ∈ Submission.Blueprint.twoPoint H t, ∀ k ∈ Work.ThmF.Ksub H t,
      d * k * d⁻¹ ∈ Work.ThmF.Ksub H t := by
    intro d hd k hk
    have hkd : t * k * t⁻¹ = k⁻¹ := ((hKm k).mp hk).2
    have htd : t * d * t⁻¹ ∈ Submission.Blueprint.twoPoint H t := htmem d hd
    have hgD : d⁻¹ * (t * d * t⁻¹) ∈ Submission.Blueprint.twoPoint H t :=
      (Submission.Blueprint.twoPoint H t).mul_mem
        ((Submission.Blueprint.twoPoint H t).inv_mem hd) htd
    -- `g := d⁻¹ (t d t⁻¹)` is inverted by `t`, hence lies in `K̄`
    have hginv : t * (d⁻¹ * (t * d * t⁻¹)) * t⁻¹ = (d⁻¹ * (t * d * t⁻¹))⁻¹ := by
      have hh : MulAut.conj t * MulAut.conj t = 1 := by
        rw [← map_mul, ht2, map_one]
      have h1 : (MulAut.conj t) (d⁻¹ * (MulAut.conj t) d) = ((MulAut.conj t) d)⁻¹ * d := by
        rw [map_mul, map_inv]
        have h2 : (MulAut.conj t) ((MulAut.conj t) d) = d := by
          rw [← MulAut.mul_apply, hh, MulAut.one_apply]
        rw [h2]
      rw [show t * (d⁻¹ * (t * d * t⁻¹)) * t⁻¹
            = (MulAut.conj t) (d⁻¹ * (MulAut.conj t) d) by
            simp only [MulAut.conj_apply]]
      rw [h1, MulAut.conj_apply]
      group
    have hg : d⁻¹ * (t * d * t⁻¹) ∈ Work.ThmF.Ksub H t := (hKm _).mpr ⟨hgD, hginv⟩
    have hk' : k⁻¹ ∈ Work.ThmF.Ksub H t := (Work.ThmF.Ksub H t).inv_mem hk
    have hc := hab _ hg _ hk'
    have keyeq : (t * d * t⁻¹) * k⁻¹ * (t * d * t⁻¹)⁻¹ = d * k⁻¹ * d⁻¹ := by
      have hgconj : d⁻¹ * (t * d * t⁻¹) * k⁻¹ * (d⁻¹ * (t * d * t⁻¹))⁻¹ = k⁻¹ := by
        rw [hc]; group
      calc (t * d * t⁻¹) * k⁻¹ * (t * d * t⁻¹)⁻¹
          = d * (d⁻¹ * (t * d * t⁻¹) * k⁻¹ * (d⁻¹ * (t * d * t⁻¹))⁻¹) * d⁻¹ := by group
        _ = d * k⁻¹ * d⁻¹ := by rw [hgconj]
    exact (hKm _).mpr ⟨
      (Submission.Blueprint.twoPoint H t).mul_mem
        ((Submission.Blueprint.twoPoint H t).mul_mem hd (hle hk))
        ((Submission.Blueprint.twoPoint H t).inv_mem hd),
      by
        rw [show t * (d * k * d⁻¹) * t⁻¹
              = (t * d * t⁻¹) * k⁻¹ * (t * d * t⁻¹)⁻¹ by
              rw [show t * (d * k * d⁻¹) * t⁻¹
                    = (t * d * t⁻¹) * (t * k * t⁻¹) * (t * d⁻¹ * t⁻¹) by group, hkd]
              group]
        rw [keyeq]
        group⟩
  have hDN : Submission.Blueprint.twoPoint H t ≤
      Subgroup.normalizer (Work.ThmF.Ksub H t : Set G) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; exact key d hd x hx
    · intro hx
      have hx' := key d⁻¹ ((Submission.Blueprint.twoPoint H t).inv_mem hd) (d * x * d⁻¹) hx
      rwa [show d⁻¹ * (d * x * d⁻¹) * (d⁻¹)⁻¹ = x by group] at hx'
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Work.ThmF.Ksub_le_twoPoint t)).mpr hDN

end Work.ThmF.ChV12
