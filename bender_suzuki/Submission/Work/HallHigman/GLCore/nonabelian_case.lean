import Mathlib
import Submission.Work.HallHigman.GLCore.Defs
import Submission.Work.HallHigman.GLCore.nonabelian_structure
import Submission.Work.HallHigman.GLCore.exists_scalar_of_commute_irreducible
import Submission.Work.HallHigman.GLCore.fourier_finrank
import Submission.Work.HallHigman.GLCore.sq_finrank_le_mul_finrank_commutant
import Submission.Work.HallHigman.GLCore.hh_arith
import Submission.Work.HallHigman.GLCore.dvd_centerQuotient_sub_one
import Submission.Work.HallHigman.GLCore.p_mul_finrank_commutant_le
import Submission.Work.HallHigman.GLCore.exists_square_eq_card_centerQuotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.HallHigman.GLCore

open scoped commutatorElement

/-- The commutant of `X` and of `X - 1` agree. -/
lemma commutant_sub_one_eq {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (X : Module.End K V) :
    Work.HallHigman.commutant (X - 1) = Work.HallHigman.commutant X := by
  ext Y
  rw [Work.HallHigman.mem_commutant_iff, Work.HallHigman.mem_commutant_iff]
  constructor
  · intro h
    have h2 : X * Y - 1 * Y = Y * X - Y * 1 := by
      rw [← sub_mul, ← mul_sub]
      exact h
    rw [one_mul, mul_one] at h2
    have h3 : X * Y - Y + Y = Y * X - Y + Y := congrArg (fun t => t + Y) h2
    simpa using h3
  · intro h
    rw [sub_mul, mul_sub, h, one_mul, mul_one]

/-- **L13 of the GL-core design** (Steps 4b–4f, the non-abelian case of the proof of
Hall--Higman B, see `NOTES_LEAD_ft_hallhigman.md` §2.2): with the core hypotheses, `V` irreducible
for `𝒬 ∪ {X}`, `𝒬` a non-abelian `q`-group satisfying the minimality hypothesis, the conclusion
`(X - 1) ^ (p - 1) ≠ 0` holds.

Proof: `Z(𝒬)` is `X`-central and acts by scalars (L6); `C_𝒬(X) ≤ Z(𝒬)` and `⁅𝒬,𝒬⁆ ≤ Z(𝒬)`, and `X`
acts fixed-point-freely on `𝒬/Z(𝒬)` (L5); the Fourier lemma (L8, `fourier_finrank`) applies to any
`𝒬`-simple submodule `W` (Schur, L7, gives `dim End_𝒬(W) = 1`, hence `|𝒬/Z(𝒬)| = s²` with
`s = dim W` odd), and to `V` (giving `D² = s²·b`, `D = dim V`, `b = dim End_𝒬(V)`); the `Ad X`-orbit
count gives `p·dim C(X) ≤ (p + s² - 1)·b`; the commutant bound (L10,
`sq_finrank_le_mul_finrank_commutant`) gives `D² ≤ (p-1)·dim C(X)`; and L11 (`hh_arith`) closes.
The prover may establish the group-theoretic facts of `nonabelian_structure` (L5) and the orbit
count as helper lemmas in its own file. -/
lemma nonabelian_case {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [IsAlgClosed K] [FiniteDimensional K V] {p : ℕ} [Fact p.Prime] [CharP K p]
    {Q : Subgroup (Module.End K V)ˣ} {X : (Module.End K V)ˣ}
    (h : Work.HallHigman.CoreHyp p Q X) (hnab : ¬ IsMulCommutative Q)
    (hirr : Work.HallHigman.IsIrreducibleFor
      ((fun a : (Module.End K V)ˣ => (a : Module.End K V)) '' (Q ∪ {X})))
    {q : ℕ} (hq : q.Prime) (hQq : IsPGroup q Q)
    (hmin : ∀ R : Subgroup (Module.End K V)ˣ, R < Q →
      (∀ a ∈ R, X * a * X⁻¹ ∈ R) → ∀ a ∈ R, a * X = X * a) :
    ((X : Module.End K V) - 1) ^ (p - 1) ≠ 0 := by
  classical
  intro hfail
  haveI hQfin : Finite ↥Q := h.finite
  haveI hVnt : Nontrivial V := hirr.1
  let σ : ↥Q →* Module.End K V := (Units.coeHom (Module.End K V)).comp Q.subtype
  have hσ_apply : ∀ a : ↥Q,
      σ a = (((a : ↥Q) : (Module.End K V)ˣ) : Module.End K V) := fun a => rfl
  -- L5
  obtain ⟨hcent, hcommQQ, hfpfQ⟩ :=
    nonabelian_structure (p := p) (Q := Q) X h.pow h.norm h.cop hmin h.noncomm hq hQq hnab
  -- the automorphism of `Q` given by conjugation by `X`
  let f : ↥Q →* ↥Q :=
    { toFun := fun a => ⟨X * (a : (Module.End K V)ˣ) * X⁻¹, h.norm a a.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hf_inj : Function.Injective f := by
    intro a b hab
    have h1 : X * (a : (Module.End K V)ˣ) * X⁻¹ = X * (b : (Module.End K V)ˣ) * X⁻¹ :=
      congrArg (fun u : ↥Q => (u : (Module.End K V)ˣ)) hab
    have h2 := congrArg (fun u : (Module.End K V)ˣ => X⁻¹ * u * X) h1
    group at h2
    exact Subtype.ext h2
  let α : ↥Q ≃* ↥Q := MulEquiv.ofBijective f ⟨hf_inj, Finite.surjective_of_injective hf_inj⟩
  have hα_val : ∀ a : ↥Q,
      ((α a : ↥Q) : (Module.End K V)ˣ) = X * (a : (Module.End K V)ˣ) * X⁻¹ := fun a => rfl
  have hα_iter : ∀ (k : ℕ) (a : ↥Q),
      (((α ^ k) a : ↥Q) : (Module.End K V)ˣ)
        = X ^ k * (a : (Module.End K V)ˣ) * (X ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
        intro a
        have h1 : ((α ^ (k + 1)) a : ↥Q) = (α ^ k) (α a) := by
          rw [pow_succ]; rfl
        rw [h1, ih (α a), hα_val a]
        group
  have hαp : α ^ p = 1 := by
    refine MulEquiv.ext (fun a => ?_)
    refine Subtype.ext ?_
    rw [hα_iter p a, h.pow]
    simp
  have hα : ∀ e : ↥Q, σ (α e) = X * σ e * X⁻¹ := by
    intro e
    rw [hσ_apply (α e), hσ_apply e]
    exact congrArg (fun u : (Module.End K V)ˣ => (u : Module.End K V)) (hα_val e)
  -- the centre of `Q`
  set Zamb : Subgroup (Module.End K V)ˣ := (Subgroup.center ↥Q).map Q.subtype with hZambdef
  have hα_center : ∀ z ∈ Subgroup.center ↥Q, α z ∈ Subgroup.center ↥Q := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨u, rfl⟩ := α.surjective w
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz u]
  have hZinv : ∀ a ∈ Zamb, X * a * X⁻¹ ∈ Zamb := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp ha
    exact Subgroup.mem_map.mpr ⟨α z, hα_center z hz, hα_val z⟩
  have hZle : Zamb ≤ Q := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp ha
    exact z.2
  have hZlt : Zamb < Q := by
    refine lt_of_le_of_ne hZle ?_
    intro heq
    apply hnab
    rw [isMulCommutative_iff]
    intro g w
    have hg : ((g : ↥Q) : (Module.End K V)ˣ) ∈ Zamb := by rw [heq]; exact g.2
    obtain ⟨z, hz, hzg⟩ := Subgroup.mem_map.mp hg
    have hzg' : z = g := Subtype.ext hzg
    subst hzg'
    exact (Subgroup.mem_center_iff.mp hz w).symm
  have hZcomm : ∀ a ∈ Zamb, a * X = X * a := hmin Zamb hZlt hZinv
  have hαZ : ∀ z ∈ Subgroup.center ↥Q, α z = z := by
    intro z hz
    refine Subtype.ext ?_
    have hzZ : ((z : ↥Q) : (Module.End K V)ˣ) ∈ Zamb := Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    have hcz := hZcomm _ hzZ
    rw [hα_val z, ← hcz]
    group
  -- Fourier hypotheses for `E = Q` acting on `V`
  have hsc : ∀ z ∈ Subgroup.center ↥Q, ∃ c : K, σ z = algebraMap K (Module.End K V) c := by
    intro z hz
    have hzZ : ((z : ↥Q) : (Module.End K V)ˣ) ∈ Zamb := Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    have hzX : σ z * (X : Module.End K V) = (X : Module.End K V) * σ z := by
      rw [hσ_apply z]
      exact congrArg (fun u : (Module.End K V)ˣ => (u : Module.End K V)) (hZcomm _ hzZ)
    have hzz : ∀ s ∈ ((fun a : (Module.End K V)ˣ => (a : Module.End K V)) '' (Q ∪ {X})),
        Commute (σ z) s := by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := hs
      rcases ha with haQ | haX
      · have h1 : (z : (Module.End K V)ˣ) * a = a * (z : (Module.End K V)ˣ) := by
          have h2 := Subgroup.mem_center_iff.mp hz ⟨a, haQ⟩
          have h3 := congrArg (fun u : ↥Q => (u : (Module.End K V)ˣ)) h2
          simpa using h3.symm
        rw [hσ_apply z]
        exact congrArg (fun u : (Module.End K V)ˣ => (u : Module.End K V)) h1
      · rw [Set.mem_singleton_iff] at haX
        subst haX
        exact hzX
    obtain ⟨c, hc⟩ := exists_scalar_of_commute_irreducible
      ((fun a : (Module.End K V)ˣ => (a : Module.End K V)) '' (Q ∪ {X})) hirr (σ z) hzz
    exact ⟨c, hc⟩
  have hfaith : ∀ z ∈ Subgroup.center ↥Q, σ z = 1 → z = 1 := by
    intro z hz hz1
    have h1 : ((z : (Module.End K V)ˣ) : Module.End K V) = 1 := by
      rw [← hσ_apply z]
      exact hz1
    have h2 : (z : (Module.End K V)ˣ) = 1 := Units.ext h1
    exact Subtype.ext h2
  have hcomm : ∀ e f' : ↥Q, e * f' * e⁻¹ * f'⁻¹ ∈ Subgroup.center ↥Q := by
    intro e f'
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hmem : ((e * f' * e⁻¹ * f'⁻¹ : ↥Q) : (Module.End K V)ˣ) ∈
        Subgroup.centralizer (Q : Set (Module.End K V)ˣ) := by
      have h0 := hcommQQ (Subgroup.commutator_mem_commutator (H₁ := Q) (H₂ := Q) e.2 f'.2)
      simpa [commutatorElement_def] using h0
    have h2 := (Subgroup.mem_centralizer_iff.mp hmem) (w : (Module.End K V)ˣ) w.2
    simpa using h2
  have hE : (Nat.card ↥Q : K) ≠ 0 := by
    intro h0
    exact h.cop ((CharP.cast_eq_zero_iff K p (Nat.card ↥Q)).mp h0)
  have hfpf : ∀ e : ↥Q, α e * e⁻¹ ∈ Subgroup.center ↥Q → e ∈ Subgroup.center ↥Q := by
    intro e he
    have hc : ((α e * e⁻¹ : ↥Q) : (Module.End K V)ˣ) ∈
        Subgroup.centralizer (Q : Set (Module.End K V)ˣ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h2 := Subgroup.mem_center_iff.mp he ⟨g, hg⟩
      have h3 := congrArg (fun u : ↥Q => (u : (Module.End K V)ˣ)) h2
      simpa using h3
    have hcX : X * (e : (Module.End K V)ˣ) * X⁻¹ * (e : (Module.End K V)ˣ)⁻¹ ∈
        Subgroup.centralizer (Q : Set (Module.End K V)ˣ) := by
      rw [← hα_val e]
      simpa using hc
    have hQe : (e : (Module.End K V)ˣ) ∈ Subgroup.centralizer (Q : Set (Module.End K V)ˣ) :=
      hfpfQ (e : (Module.End K V)ˣ) e.2 hcX
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 := (Subgroup.mem_centralizer_iff.mp hQe) (g : (Module.End K V)ˣ) g.2
    exact Subtype.ext (by simpa using h2)
  -- the conclusion
  by_cases hp2 : p = 2
  · subst hp2
    have hEnd : (X : Module.End K V) = 1 := sub_eq_zero.mp (by simpa using hfail)
    have hXone : X = 1 := Units.ext hEnd
    obtain ⟨a, ha, hne⟩ := h.noncomm
    exact hne (by rw [hXone, mul_one, one_mul])
  · have hL8 := fourier_finrank σ hsc hfaith hcomm hE
    obtain ⟨s, hsodd, hs1, hssq⟩ :=
      exists_square_eq_card_centerQuotient h hnab hirr hq hQq hmin
    have hdimeq : Module.finrank K V ^ 2
        = Nat.card (↥Q ⧸ Subgroup.center ↥Q) *
            Module.finrank K (Work.HallHigman.commutantOf σ) := by
      rw [← hL8, Module.finrank_linearMap K K V V, pow_two]
    have hU0 := p_mul_finrank_commutant_le σ hsc hfaith hcomm hE α X hα hαZ hfpf h.pow
    rw [← hssq] at hU0
    have hF : Module.finrank K V ^ 2
        = s ^ 2 * Module.finrank K (Work.HallHigman.commutantOf σ) := by
      rw [hdimeq, ← hssq]
    have hdvd : p ∣ s ^ 2 - 1 := by
      have h := dvd_centerQuotient_sub_one α hαp hfpf
      rwa [← hssq] at h
    have hL0 := sq_finrank_le_mul_finrank_commutant ((X : Module.End K V) - 1) hfail
    rw [Work.HallHigman.GLCore.commutant_sub_one_eq] at hL0
    have hbpos : 0 < Module.finrank K (Work.HallHigman.commutantOf σ) := by
      haveI : Nontrivial ↥(Work.HallHigman.commutantOf σ) :=
        ⟨⟨1, Work.HallHigman.one_mem_commutantOf σ⟩, ⟨0, Submodule.zero_mem _⟩, by
          intro h
          exact one_ne_zero (Subtype.ext_iff.mp h)⟩
      exact Module.finrank_pos
    exact hh_arith (p := p) (s := s) (b := Module.finrank K (Work.HallHigman.commutantOf σ))
      (D := Module.finrank K V)
      (c := Module.finrank K (Work.HallHigman.commutant (X : Module.End K V)))
      (Fact.out) hp2 hsodd hs1 hdvd hbpos hF hU0 hL0

end Work.HallHigman.GLCore
