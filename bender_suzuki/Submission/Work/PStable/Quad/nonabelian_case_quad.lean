/-
Area A11 (p-stability) of the Feit--Thompson drive: the *non-abelian* case of the quadratic
GL-core, i.e. the `(X - 1) ^ 2 = 0` analogue of `HallHigman/GLCore/nonabelian_case.lean`.

Setting (`Work.PStable.Quad.QuadCore`): `K` algebraically closed of characteristic `p`, `p ≠ 2`,
`V` a finite dimensional `K`-module, `𝒬 ≤ GL(V)` a finite `q`-group of order prime to `p` with
`X ∈ GL(V)` of order `p` normalising `𝒬`, not commuting with it, and either `p ≥ 5` or every
`2`-subgroup of `𝒬` abelian.  `V` is irreducible for `𝒬 ∪ {X}`, `𝒬` is non-abelian, and every
proper `X`-invariant subgroup of `𝒬` commutes with `X` (minimality).  Conclusion:
`(X - 1) ^ 2 ≠ 0`.

Proof.  Assume `(X - 1) ^ 2 = 0`.

* If `q ≠ 2` then `|𝒬|` is odd, so the odd-order theorem
  `Work.HallHigman.GLCore.nonabelian_case` applies (via `CoreHyp.ofQuadCore`) and gives the
  stronger `(X - 1) ^ (p - 1) ≠ 0`, which the quadratic hypothesis contradicts since `p ≥ 3`.
* If `q = 2` and `p = 3` then `𝒬` is a `2`-group and the second disjunct of `QuadCore.two`
  makes it abelian, contradiction.
* If `q = 2` and `p ≥ 5` we run the quadratic argument directly: with `σ` the defining
  representation of `𝒬`, `n = |𝒬 / Z(𝒬)|`, `b = dim End_𝒬(V)`, `c = dim C_{End V}(X)` and
  `D = dim V`, the lemmas of `HallHigman/GLCore` give
  `D ^ 2 = n * b` (`fourier_finrank`), `p * c ≤ (p + n - 1) * b`
  (`p_mul_finrank_commutant_le`), `D ^ 2 ≤ 2 * c`
  (`sq_finrank_le_mul_finrank_commutant`, with `r = 2`), and `p ∣ n - 1`
  (`dvd_centerQuotient_sub_one`).  Since `𝒬` is non-abelian, `n ≥ 2`, and `p ≥ 5` then rules
  these out (`Work.PStable.Quad.quad_arith_p5`): the quadratic lower bound forces `n ≤ 3`, and
  `p ∣ n - 1` with `n ≤ 3` forces `p ≤ 2`.

Note that, unlike the odd-order case, no oddness of `|𝒬|` (nor that `n` is a perfect square) is
used: the sharper bound `r = 2` replaces the Hall--Higman `r = p - 1`.
-/
import Mathlib
import Submission.Work.PStable.Quad.Defs
import Submission.Work.PStable.Quad.Arith
import Submission.Work.HallHigman.GLCore.Defs
import Submission.Work.HallHigman.GLCore.nonabelian_case
import Submission.Work.HallHigman.GLCore.nonabelian_structure
import Submission.Work.HallHigman.GLCore.fourier_finrank
import Submission.Work.HallHigman.GLCore.p_mul_finrank_commutant_le
import Submission.Work.HallHigman.GLCore.sq_finrank_le_mul_finrank_commutant

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.PStable.Quad

open scoped commutatorElement

/-- A group whose top subgroup is commutative is commutative. -/
private lemma isMulCommutative_of_top {G : Type*} [Group G]
    (h : IsMulCommutative ↥(⊤ : Subgroup G)) : IsMulCommutative G := by
  rw [isMulCommutative_iff] at h ⊢
  intro a b
  exact congrArg Subtype.val (h ⟨a, trivial⟩ ⟨b, trivial⟩)

theorem nonabelian_case_quad {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [IsAlgClosed K] [FiniteDimensional K V] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {Q : Subgroup (Module.End K V)ˣ} {X : (Module.End K V)ˣ}
    (h : Work.PStable.Quad.QuadCore p Q X) (hnab : ¬ IsMulCommutative Q)
    (hirr : Work.HallHigman.IsIrreducibleFor
      ((fun a : (Module.End K V)ˣ => (a : Module.End K V)) '' (Q ∪ {X})))
    {q : ℕ} (hq : q.Prime) (hQq : IsPGroup q Q)
    (hmin : ∀ R : Subgroup (Module.End K V)ˣ, R < Q →
      (∀ a ∈ R, X * a * X⁻¹ ∈ R) → ∀ a ∈ R, a * X = X * a) :
    ((X : Module.End K V) - 1) ^ 2 ≠ 0 := by
  classical
  intro hfail
  haveI hQfin : Finite ↥Q := h.finite
  haveI hVnt : Nontrivial V := hirr.1
  have hp3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
  by_cases hq2 : q = 2
  · -- Case `q = 2`: either `p = 3` and `𝒬` is abelian, or `p ≥ 5` and we argue directly.
    subst hq2
    by_cases hp5 : 5 ≤ p
    · -- `p ≥ 5`: the quadratic argument.
      let σ : ↥Q →* Module.End K V := (Units.coeHom (Module.End K V)).comp Q.subtype
      have hσ_apply : ∀ a : ↥Q,
          σ a = (((a : ↥Q) : (Module.End K V)ˣ) : Module.End K V) := fun a => rfl
      -- L5 of the GL-core design
      obtain ⟨hcent, hcommQQ, hfpfQ⟩ :=
        Work.HallHigman.GLCore.nonabelian_structure (p := p) (Q := Q) X h.pow h.norm h.cop hmin
          h.noncomm hq hQq hnab
      -- the automorphism of `𝒬` given by conjugation by `X`
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
      -- the centre of `𝒬`
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
      -- Schur: the centre of `𝒬` acts on `V` by scalars
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
        obtain ⟨c, hc⟩ := Work.HallHigman.GLCore.exists_scalar_of_commute_irreducible
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
        have hQe : (e : (Module.End K V)ˣ) ∈
            Subgroup.centralizer (Q : Set (Module.End K V)ˣ) :=
          hfpfQ (e : (Module.End K V)ˣ) e.2 hcX
        rw [Subgroup.mem_center_iff]
        intro g
        have h2 := (Subgroup.mem_centralizer_iff.mp hQe) (g : (Module.End K V)ˣ) g.2
        exact Subtype.ext (by simpa using h2)
      -- the Fourier decomposition and the two dimension bounds
      have hL8 := Work.HallHigman.GLCore.fourier_finrank σ hsc hfaith hcomm hE
      have hU0 := Work.HallHigman.GLCore.p_mul_finrank_commutant_le σ hsc hfaith hcomm hE
        α X hα hαZ hfpf h.pow
      have hdvd := Work.HallHigman.GLCore.dvd_centerQuotient_sub_one α hαp hfpf
      have hL0 := Work.HallHigman.GLCore.sq_finrank_le_mul_finrank_commutant
        ((X : Module.End K V) - 1) hfail
      rw [Work.HallHigman.GLCore.commutant_sub_one_eq] at hL0
      have hF : Module.finrank K V ^ 2
          = Nat.card (↥Q ⧸ Subgroup.center ↥Q) *
              Module.finrank K (Work.HallHigman.commutantOf σ) := by
        rw [← hL8, Module.finrank_linearMap K K V V, pow_two]
      have hbpos : 0 < Module.finrank K (Work.HallHigman.commutantOf σ) := by
        haveI : Nontrivial ↥(Work.HallHigman.commutantOf σ) :=
          ⟨⟨1, Work.HallHigman.one_mem_commutantOf σ⟩, ⟨0, Submodule.zero_mem _⟩, by
            intro h
            exact one_ne_zero (Subtype.ext_iff.mp h)⟩
        exact Module.finrank_pos
      have hn2 : 2 ≤ Nat.card (↥Q ⧸ Subgroup.center ↥Q) := by
        have hnetop : Subgroup.center ↥Q ≠ ⊤ := fun htop =>
          hnab (Subgroup.center_eq_top_iff.mp htop)
        have hlt : 1 < (Subgroup.center ↥Q).index := Subgroup.one_lt_index_of_ne_top hnetop
        rw [Subgroup.index_eq_card] at hlt
        omega
      refine quad_arith_p5
        (c := Module.finrank K (Work.HallHigman.commutant (X : Module.End K V)))
        hp5 hn2 hbpos ?_ ?_ hdvd
      · refine le_trans hU0 ?_
        exact Nat.mul_le_mul_right _ (by omega)
      · rw [← hF]
        exact hL0
    · -- `p < 5` (so `p = 3`) and `q = 2`: `𝒬` is a `2`-group, and `QuadCore.two` says that
      -- every `2`-subgroup of `𝒬` is abelian, in particular `𝒬` itself.
      rcases h.two with h5 | hab
      · exact absurd h5 hp5
      · have htop2 : IsPGroup 2 ↥(⊤ : Subgroup ↥Q) :=
          IsPGroup.of_equiv hQq (Subgroup.topEquiv (G := ↥Q)).symm
        haveI : IsMulCommutative ↥(⊤ : Subgroup ↥Q) := hab ⊤ htop2
        exact hnab (isMulCommutative_of_top inferInstance)
  · -- Case `q ≠ 2`: `|𝒬|` is odd and the odd-order theorem applies
    have hodd : Odd (Nat.card ↥Q) := odd_card_of_isPGroup hq hq2 hQq
    have hcore : Work.HallHigman.CoreHyp p Q X :=
      Work.HallHigman.CoreHyp.ofQuadCore h hodd
    have hne := Work.HallHigman.GLCore.nonabelian_case (p := p) hcore hnab hirr hq hQq hmin
    refine hne ?_
    rw [show p - 1 = 2 + (p - 3) by omega, pow_add, hfail, zero_mul]

end Work.PStable.Quad
