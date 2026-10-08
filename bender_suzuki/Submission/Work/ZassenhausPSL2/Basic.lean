import Submission.Work.ZassenhausPSL2.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open scoped Pointwise

namespace Work.ZassenhausPSL2

variable {G : Type*} [Group G] [Finite G]
variable {H Q : Subgroup G} {t : G}

/-- `t` has order two, so `t * t = 1` and `t⁻¹ = t`. -/
lemma t_mul_t (h : IsSplitRankOne H Q t) : t * t = 1 := by
  rw [← pow_two, ← h.invol]
  exact pow_orderOf_eq_one t

lemma t_inv (h : IsSplitRankOne H Q t) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right (t_mul_t h)

lemma t_conj_invol (h : IsSplitRankOne H Q t) (x : G) : t * (t * x * t) * t = x := by
  calc t * (t * x * t) * t = t * t * x * (t * t) := by simp only [mul_assoc]
    _ = x := by rw [t_mul_t h, one_mul, mul_one]

/-- `D = H ∩ H^t` is invariant under conjugation by `t`. -/
lemma dStab_conj_mem (h : IsSplitRankOne H Q t) {d : G} (hd : d ∈ dStab H t) :
    t * d * t ∈ dStab H t := by
  constructor
  · obtain ⟨e, he, hed⟩ : ∃ e ∈ H, (MulAut.conj t) e = d := hd.2
    have h2 : t * (t * e * t) * t = e := t_conj_invol h e
    have : t * d * t = e := by rw [← hed, MulAut.conj_apply, t_inv h, h2]
    rw [this]
    exact he
  · refine ⟨d, hd.1, ?_⟩
    have hcoe : (MulEquiv.toMonoidHom (MulAut.conj t)) d = (MulAut.conj t) d := rfl
    rw [hcoe, MulAut.conj_apply, t_inv h]

/-- Writing an element of `H = Q ⋊ D` with the `D`-part on the left. -/
lemma mem_eq_dStab_mul_Q (h : IsSplitRankOne H Q t) (b : H) :
    ∃ (d : dStab H t) (q : Q), (d : G) * (q : G) = (b : G) := by
  have hQn : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mpr h.normal
  have hsup : (dStab H t).subgroupOf H ⊔ (Q.subgroupOf H) = ⊤ := by
    have hsup' : dStab H t ⊔ Q = H := by rw [sup_comm]; exact h.sup_eq
    rw [← Subgroup.subgroupOf_sup (inf_le_left : dStab H t ≤ H) h.le, hsup',
      Subgroup.subgroupOf_self]
  have hmul : (↑(⊤ : Subgroup H) : Set H) =
      ((dStab H t).subgroupOf H : Set H) * ((Q.subgroupOf H) : Set H) := by
    rw [← hsup]
    exact @Subgroup.mul_normal H _ ((dStab H t).subgroupOf H) ((Q.subgroupOf H)) hQn
  have hb : (b : H) ∈ (↑(⊤ : Subgroup H) : Set H) := trivial
  rw [hmul, Set.mem_mul] at hb
  obtain ⟨d, hd, q, hq, hdq⟩ := hb
  have hdqG : (d : G) * (q : G) = (b : G) := by
    have := congrArg (fun z : ↥H => (z : G)) hdq
    simpa using this
  exact ⟨⟨(d : G), Subgroup.mem_subgroupOf.mp hd⟩,
    ⟨(q : G), Subgroup.mem_subgroupOf.mp hq⟩, hdqG⟩

/-- Uniqueness in the canonical form. -/
lemma decomp_unique (h : IsSplitRankOne H Q t) {a a' : H} {q q' : Q} {g : G}
    (ha : (a : G) * t * (q : G) = g) (ha' : (a' : G) * t * (q' : G) = g) :
    (a, q) = (a', q') := by
  have ht2 := t_mul_t h
  have hti := t_inv h
  have h0 : (a' : G)⁻¹ * (a : G) * t * (q : G) = t * (q' : G) := by
    have h1 : (a' : G)⁻¹ * ((a : G) * t * (q : G)) =
        (a' : G)⁻¹ * ((a' : G) * t * (q' : G)) := by rw [ha, ha']
    simpa [mul_assoc] using h1
  have key : (a' : G)⁻¹ * (a : G) = t * ((q' : G) * (q : G)⁻¹) * t := by
    have h2 : (a' : G)⁻¹ * (a : G) * t * (q : G) * (q : G)⁻¹ =
        t * (q' : G) * (q : G)⁻¹ := congrArg (· * (q : G)⁻¹) h0
    have h3 : (a' : G)⁻¹ * (a : G) * t = t * (q' : G) * (q : G)⁻¹ := by
      simpa [mul_assoc] using h2
    have h4 : (a' : G)⁻¹ * (a : G) * t * t = t * (q' : G) * (q : G)⁻¹ * t :=
      congrArg (· * t) h3
    simpa [mul_assoc, ht2, hti] using h4
  have hH : t * ((q' : G) * (q : G)⁻¹) * t ∈ H := by
    rw [← key]
    exact mul_mem (inv_mem a'.2) a.2
  have hQ : (q' : G) * (q : G)⁻¹ ∈ Q := mul_mem q'.2 (inv_mem q.2)
  have hD : (q' : G) * (q : G)⁻¹ ∈ dStab H t := by
    constructor
    · exact h.le hQ
    · have hconj : (MulAut.conj t) (t * ((q' : G) * (q : G)⁻¹) * t) =
          (q' : G) * (q : G)⁻¹ := by
        rw [MulAut.conj_apply, hti]
        exact t_conj_invol h ((q' : G) * (q : G)⁻¹)
      exact ⟨_, hH, hconj⟩
  have hone : (q' : G) * (q : G)⁻¹ = 1 := by
    have : (q' : G) * (q : G)⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← h.inf_eq]
      exact ⟨hQ, hD⟩
    simpa using this
  have hqq : (q' : G) = (q : G) := mul_inv_eq_one.mp hone
  have haa : (a' : G) = (a : G) := by
    have hdone : (a' : G)⁻¹ * (a : G) = 1 := by
      rw [key, hqq, mul_inv_cancel]
      simp [ht2]
    exact inv_mul_eq_one.mp hdone
  exact Prod.ext (Subtype.ext haa.symm) (Subtype.ext hqq.symm)

/-- **Canonical form.** In a split rank-one group, every element outside `H` is uniquely
`h * t * q` with `h ∈ H` and `q ∈ Q` (Peterfalvi II, Ch. V §2 Lemma 1 a). -/
theorem exists_unique_decomp (h : IsSplitRankOne H Q t) {g : G} (hg : g ∉ H) :
    ∃! p : H × Q, (p.1 : G) * t * (p.2 : G) = g := by
  have ht2 := t_mul_t h
  have hti := t_inv h
  have hex : ∃ p : H × Q, (p.1 : G) * t * (p.2 : G) = g := by
    have hHg : (((1 : G)) : G ⧸ H) ≠ ((g : G) : G ⧸ H) := by
      intro hcon
      refine hg ?_
      have := QuotientGroup.eq.mp hcon
      simpa using this
    have htg : (((t : G)) : G ⧸ H) ≠ (((1 : G)) : G ⧸ H) := by
      intro hcon
      refine h.not_mem ?_
      have := QuotientGroup.eq.mp hcon
      simpa [hti] using this
    obtain ⟨x, hx0, hx1⟩ :=
      (MulAction.is_two_pretransitive_iff.mp h.twoTransitive) hHg htg
    have h1 : t * x ∈ H := by
      have hq : ((x : G) : G ⧸ H) = ((t : G) : G ⧸ H) := by
        simpa using hx0
      have hmem : (x⁻¹ * t)⁻¹ ∈ H := inv_mem (QuotientGroup.eq.mp hq)
      have : (x⁻¹ * t)⁻¹ = t * x := by rw [mul_inv_rev, hti, inv_inv]
      rwa [this] at hmem
    have h2 : x * g ∈ H := by
      have hq : ((x * g : G) : G ⧸ H) = (((1 : G)) : G ⧸ H) := by
        simpa using hx1
      have : (x * g)⁻¹ * 1 ∈ H := QuotientGroup.eq.mp hq
      simpa using inv_mem this
    have hxinv : (t * x)⁻¹ * t = x⁻¹ := by
      rw [mul_inv_rev, hti, mul_assoc, ht2, mul_one]
    have hg' : g = (t * x)⁻¹ * t * (x * g) := by rw [hxinv]; group
    obtain ⟨d, q, hdq⟩ := mem_eq_dStab_mul_Q h ⟨x * g, h2⟩
    have hdq' : (d : G) * (q : G) = x * g := hdq
    have hmem : (t * x)⁻¹ * (t * (d : G) * t) ∈ H :=
      mul_mem (inv_mem h1) (Subgroup.mem_inf.mp (dStab_conj_mem h d.2)).1
    refine ⟨(⟨(t * x)⁻¹ * (t * (d : G) * t), hmem⟩, q), ?_⟩
    have hdt : (t * (d : G) * t) * t = t * (d : G) := by
      calc (t * (d : G) * t) * t = t * (d : G) * (t * t) := by simp only [mul_assoc]
        _ = t * (d : G) := by rw [ht2, mul_one]
    calc ((⟨(t * x)⁻¹ * (t * (d : G) * t), hmem⟩ : H) : G) * t * (q : G)
        = (t * x)⁻¹ * (t * (d : G) * t) * t * (q : G) := by rw [Subtype.coe_mk]
      _ = (t * x)⁻¹ * (t * (d : G) * t * t) * (q : G) := by simp only [mul_assoc]
      _ = (t * x)⁻¹ * (t * (d : G)) * (q : G) := by rw [hdt]
      _ = (t * x)⁻¹ * t * ((d : G) * (q : G)) := by simp only [mul_assoc]
      _ = (t * x)⁻¹ * t * (x * g) := by rw [← hdq']
      _ = g := by rw [← hg']
  exact ⟨hex.choose, hex.choose_spec, fun p hp => decomp_unique h hp hex.choose_spec⟩

/-- `t x t ∉ H` for `x ∈ Q#`: otherwise `x ∈ Q ∩ H^t ⊆ Q ∩ D = 1`. -/
lemma t_conj_notMem (h : IsSplitRankOne H Q t) {x : Q} (hx : (x : G) ≠ 1) :
    t * (x : G) * t ∉ H := by
  intro hmem
  have hx' : (x : G) ∈ conj t H := by
    refine ⟨t * (x : G) * t, hmem, ?_⟩
    have hcoe : (MulEquiv.toMonoidHom (MulAut.conj t)) (t * (x : G) * t)
        = (MulAut.conj t) (t * (x : G) * t) := rfl
    rw [hcoe, MulAut.conj_apply, t_inv h]
    exact t_conj_invol h (x : G)
  have : (x : G) ∈ (⊥ : Subgroup G) := by
    rw [← h.inf_eq]
    exact ⟨x.2, h.le x.2, hx'⟩
  exact hx (by simpa using this)

/-- **Existence of the canonical structure maps** `f`, `g`, `h` of a split rank-one group. -/
theorem canon_exists (h : IsSplitRankOne H Q t) : Nonempty (Canon H Q t) := by
  classical
  set W : Q → H × Q := fun x => if hx : (x : G) = 1 then (1, 1)
      else Classical.choose (exists_unique_decomp h (t_conj_notMem h hx)) with hWdef
  have hWspec : ∀ x : Q, (x : G) ≠ 1 →
      ((W x).1 : G) * t * ((W x).2 : G) = t * (x : G) * t := by
    intro x hx
    rw [hWdef]
    simp only [dif_neg hx]
    exact (Classical.choose_spec (exists_unique_decomp h (t_conj_notMem h hx))).1
  choose dd qq hdq using fun x : Q => mem_eq_dStab_mul_Q h (W x).1
  have hDnormQ : dStab H t ≤ Subgroup.normalizer (Q : Set G) :=
    le_trans inf_le_left h.normal
  refine ⟨{
    f := fun x => (W x).2
    g := fun x => ⟨(dd x : G) * (qq x : G) * (dd x : G)⁻¹,
      (Subgroup.le_normalizer_iff.mp hDnormQ) (dd x) (dd x).2 (qq x) (qq x).2⟩
    h := fun x => dd x
    spec := ?_ }⟩
  intro x hx
  have h1 : ((W x).1 : G) * t * ((W x).2 : G) = t * (x : G) * t := hWspec x hx
  have h2 : ((W x).1 : G) = (dd x : G) * (qq x : G) := (hdq x).symm
  have h3 : (dd x : G) * (qq x : G) * (dd x : G)⁻¹ * (dd x : G)
      = (dd x : G) * (qq x : G) := by group
  show t * (x : G) * t =
    (dd x : G) * (qq x : G) * (dd x : G)⁻¹ * (dd x : G) * t * ((W x).2 : G)
  rw [h3, ← h2, h1]

end Work.ZassenhausPSL2
