/-
# Conjugating Sylow subgroups with a cyclic `U`

Peterfalvi, *Le théorème de Bender–Suzuki I*, Ch. III §1.  The lemma proved here is the
Frattini/`N/C` step in the study of `p`-control groups: if `U ≤ W` is **cyclic** and `S`, `T`
are Sylow `p`-subgroups of `N_G(U) ∩ W`, then `S` and `T` are conjugate by an element of
`C_G(U) ∩ W`.

The mathematical content is the following.  Write `M = N_G(U) ∩ W` and `H = C_G(U) ∩ W`; then
`H = C_M(U)` and `U ⊴ M`, so `H ⊴ M`.  Conjugation gives a monomorphism `M/H ↪ Aut(U)`, and
`Aut(U)` is abelian because `U` is cyclic, so `M/H` is abelian.  We record this as
`Work.NormalComplement.comm_mem_centralizer_of_isCyclic` (the commutator of two normalizer
elements centralizes `U`).  The main group-theoretic engine
(`exists_conj_sylow_of_normal_abelian`, resting on
`Work.NormalComplement.sylow_conj_of_commutative_quotient`) then says that whenever `N ⊴ M` and
`M/N` is abelian, the Sylow `p`-subgroups of `M` are conjugate by an element of `N`.

Everything here is stated for subgroups of an ambient group `G`; `S.map (MulAut.conj z).toMonoidHom`
is Peterfalvi's `S^z` (left action), matching the rest of the area.
-/
import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.comm_mem_centralizer_of_isCyclic
import Submission.Work.NormalComplement.sylow_conj_of_commutative_quotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.NormalComplement

-- `haveI` is used for local instances, and some hypotheses are kept for readability only.
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- Conjugation of a subgroup expressed through the pointwise action equals `Subgroup.map` of the
corresponding `MulAut`: `S^z = S.map (MulAut.conj z).toMonoidHom`. -/
theorem map_conj_eq_pointwise_smul {G : Type*} [Group G] (S : Subgroup G) (x : G) :
    S.map (MulAut.conj x).toMonoidHom = MulAut.conj x • S := by
  rw [Subgroup.pointwise_smul_def]; rfl

/-- **Frattini step for abelian quotients.**  Let `N ≤ M` be subgroups of a finite group `G` with
`N` normal in `M` (as subgroups of `G`) and `M/N` abelian, i.e. every commutator of two elements
of `M` lies in `N`.  Then the Sylow `p`-subgroups `S`, `T` of `M` (in the ambient sense
`IsSylowIn p · M`) are conjugate by an element of `N`.

The proof passes to the group `↥M`: the Sylow subgroups become Sylow `p`-subgroups of `↥M`, the
abelian quotient is `↥M ⧸ (N.subgroupOf M)` (see
`sylow_conj_of_commutative_quotient`), and the resulting conjugating element is transported back
to `G` along `Subgroup.conj_smul_subgroupOf`. -/
theorem exists_conj_sylow_of_normal_abelian {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {N M S T : Subgroup G} (hNle : N ≤ M)
    (hNnorm : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N)
    (hcomm : ∀ a ∈ M, ∀ b ∈ M, a * b * a⁻¹ * b⁻¹ ∈ N)
    (hS : Work.NormalComplement.IsSylowIn p S M)
    (hT : Work.NormalComplement.IsSylowIn p T M) :
    ∃ n ∈ N, Subgroup.map (MulAut.conj n).toMonoidHom S = T := by
  have hSM : S ≤ M := hS.2.1
  have hTM : T ≤ M := hT.2.1
  haveI : (N.subgroupOf M).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hNnorm (g : G) g.2 (n : G) hn⟩
  have hcomm' : ∀ a b : ↥M, a * b * a⁻¹ * b⁻¹ ∈ N.subgroupOf M := by
    intro a b
    rw [Subgroup.mem_subgroupOf]
    simpa using hcomm (a : G) a.2 (b : G) b.2
  obtain ⟨n, hn⟩ := sylow_conj_of_commutative_quotient (N.subgroupOf M) hcomm'
    ((hS.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSM).symm).toSylow hS.2.2)
    ((hT.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm).toSylow hT.2.2)
  refine ⟨((n : ↥M) : G), Subgroup.mem_subgroupOf.mp n.2, ?_⟩
  have h1 : MulAut.conj (n : ↥M) • (S.subgroupOf M) = T.subgroupOf M := by
    have hc := congrArg (fun x : Sylow p ↥M => (x : Subgroup ↥M)) hn
    simpa only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] using hc
  have h2 := Subgroup.conj_smul_subgroupOf hSM (n : ↥M)
  have h3 : (MulAut.conj ((n : ↥M) : G) • S).subgroupOf M = T.subgroupOf M := by
    rw [← h2]; exact h1
  rw [Subgroup.subgroupOf_inj] at h3
  have hle : MulAut.conj ((n : ↥M) : G) • S ≤ M :=
    Subgroup.conj_smul_le_of_le hSM (n : ↥M)
  rw [inf_eq_left.mpr hle, inf_comm T M, inf_eq_right.mpr hTM] at h3
  rw [map_conj_eq_pointwise_smul]
  exact h3

theorem conj_sylow_of_isCyclic {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {W U : Subgroup G} (hUW : U ≤ W) (hcyc : IsCyclic U) {S T : Subgroup G}
    (hS : Work.NormalComplement.IsSylowIn p S (Subgroup.normalizer (U : Set G) ⊓ W))
    (hT : Work.NormalComplement.IsSylowIn p T (Subgroup.normalizer (U : Set G) ⊓ W)) :
    ∃ z : G, z ∈ Subgroup.centralizer (U : Set G) ⊓ W ∧
      Subgroup.map (MulAut.conj z).toMonoidHom S = T := by
  -- `H = C_G(U) ∩ W` is normal in `M = N_G(U) ∩ W`: a direct computation, using that the
  -- conjugate of `u ∈ U` by `m ∈ N_G(U)` lies in `U`.
  have hnorm : ∀ m ∈ Subgroup.normalizer (U : Set G) ⊓ W,
      ∀ n ∈ Subgroup.centralizer (U : Set G) ⊓ W,
      m * n * m⁻¹ ∈ Subgroup.centralizer (U : Set G) ⊓ W := by
    intro m hm n hn
    obtain ⟨hmN, hmW⟩ := hm
    obtain ⟨hnC, hnW⟩ := hn
    have h1 : m * n ∈ W := W.mul_mem hmW hnW
    have h2 : m⁻¹ ∈ W := W.inv_mem hmW
    have h3 : m * n * m⁻¹ ∈ W := W.mul_mem h1 h2
    refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, h3⟩
    intro u hu
    have hv : m⁻¹ * u * m ∈ U := by
      have h := (Subgroup.mem_normalizer_iff.mp hmN) (m⁻¹ * u * m)
      rw [show m * (m⁻¹ * u * m) * m⁻¹ = u by group] at h
      exact h.mpr hu
    have hnc := (Subgroup.mem_centralizer_iff.mp hnC) (m⁻¹ * u * m) hv
    calc u * (m * n * m⁻¹) = m * ((m⁻¹ * u * m) * n) * m⁻¹ := by group
      _ = m * (n * (m⁻¹ * u * m)) * m⁻¹ := by rw [hnc]
      _ = (m * n * m⁻¹) * u := by group
  -- `M/H` is abelian: `M/H ↪ Aut(U)` and `Aut(U)` is abelian for cyclic `U`.
  have hcom : ∀ a ∈ Subgroup.normalizer (U : Set G) ⊓ W,
      ∀ b ∈ Subgroup.normalizer (U : Set G) ⊓ W,
      a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (U : Set G) ⊓ W := by
    intro a ha b hb
    obtain ⟨haN, haW⟩ := ha
    obtain ⟨hbN, hbW⟩ := hb
    have h1 : a * b ∈ W := W.mul_mem haW hbW
    have h2 : a⁻¹ ∈ W := W.inv_mem haW
    have h3 : b⁻¹ ∈ W := W.inv_mem hbW
    have h4 : a * b * a⁻¹ ∈ W := W.mul_mem h1 h2
    exact ⟨comm_mem_centralizer_of_isCyclic hcyc haN hbN, W.mul_mem h4 h3⟩
  exact exists_conj_sylow_of_normal_abelian
    (inf_le_inf_right W (Subgroup.centralizer_le_normalizer (U : Set G))) hnorm hcom hS hT

end Work.NormalComplement
