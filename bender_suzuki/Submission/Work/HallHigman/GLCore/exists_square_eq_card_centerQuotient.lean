import Mathlib
import Submission.Work.HallHigman.GLCore.Defs
import Submission.Work.HallHigman.GLCore.nonabelian_structure
import Submission.Work.HallHigman.GLCore.exists_scalar_of_commute_irreducible
import Submission.Work.HallHigman.GLCore.finrank_commutantOf_eq_one
import Submission.Work.HallHigman.GLCore.fourier_finrank
import Submission.Work.HallHigman.GLCore.restrictRep
import Submission.Work.HallHigman.GLCore.exists_minimal_invariant_submodule
import Submission.Work.HallHigman.GLCore.isIrreducibleFor_range_restrictRep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.HallHigman.GLCore

open scoped commutatorElement

/-- The representation of a subgroup `𝒬 ≤ GL(V)` on `V`, by evaluation. -/
def coeRep {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (Q : Subgroup (Module.End K V)ˣ) : ↥Q →* Module.End K V :=
  (Units.coeHom (Module.End K V)).comp Q.subtype

@[simp] theorem coeRep_apply {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (Q : Subgroup (Module.End K V)ˣ) (z : ↥Q) :
    coeRep Q z = ((z : (Module.End K V)ˣ) : Module.End K V) := rfl

/-- **Step 4c of the GL-core design** (the "Fourier" input to the non-abelian case): under the
core hypotheses, `V` irreducible for `𝒬 ∪ {X}`, `𝒬` non-abelian, `𝒬` a `q`-group, and the
minimality hypothesis, there is a dimension `s` which is odd, `> 1`, and whose square is
`|𝒬 / Z(𝒬)|`.

Take a nonzero `𝒬`-invariant subspace `W ⊆ V` of minimal dimension (a `𝒬`-simple constituent).
Every `z ∈ Z(𝒬)` commutes with `X` by minimality (`Z(𝒬) < 𝒬` since `𝒬` is non-abelian) and with
`𝒬`, hence acts as a scalar on `V` (Schur, L6, applied to the irreducible family `𝒬 ∪ {X}`), hence
on `W`; so the Fourier lemma (L8, `fourier_finrank`) applies to `W` with `E = 𝒬` (its class-2
hypothesis `[𝒬,𝒬] ≤ Z(𝒬)` is `nonabelian_structure` (b), which uses `hq`, `hQq`, `hmin`), and
Schur (L7) on the `𝒬`-simple module `W` gives `dim End_𝒬(W) = 1`, whence `(dim W)² = |𝒬/Z(𝒬)|`.
Oddness follows since `|𝒬/Z(𝒬)|` divides the odd number `|𝒬|`, and `s > 1` since `s = 1` would
force `𝒬 = Z(𝒬)`. -/
lemma exists_square_eq_card_centerQuotient {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [IsAlgClosed K] [FiniteDimensional K V] {p : ℕ} [Fact p.Prime] [CharP K p]
    {Q : Subgroup (Module.End K V)ˣ} {X : (Module.End K V)ˣ}
    (h : Work.HallHigman.CoreHyp p Q X) (hnab : ¬ IsMulCommutative Q)
    (hirr : Work.HallHigman.IsIrreducibleFor
      ((fun a : (Module.End K V)ˣ => (a : Module.End K V)) '' (Q ∪ {X})))
    {q : ℕ} (hq : q.Prime) (hQq : IsPGroup q Q)
    (hmin : ∀ R : Subgroup (Module.End K V)ˣ, R < Q →
      (∀ a ∈ R, X * a * X⁻¹ ∈ R) → ∀ a ∈ R, a * X = X * a) :
    ∃ s : ℕ, Odd s ∧ 1 < s ∧ s ^ 2 = Nat.card (↥Q ⧸ Subgroup.center ↥Q) := by
  classical
  haveI hQfin : Finite ↥Q := h.finite
  haveI hVnt : Nontrivial V := hirr.1
  -- L5: `⁅𝒬,𝒬⁆ ≤ Z(𝒬)`
  obtain ⟨-, hcommQQ, -⟩ :=
    nonabelian_structure (p := p) (Q := Q) X h.pow h.norm h.cop hmin h.noncomm hq hQq hnab
  -- conjugation by `X` as an automorphism of `𝒬`
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
  -- the centre of `𝒬`, as a subgroup of `GL(V)`
  set Z : Subgroup (Module.End K V)ˣ := (Subgroup.center ↥Q).map Q.subtype with hZdef
  have hα_center : ∀ z ∈ Subgroup.center ↥Q, α z ∈ Subgroup.center ↥Q := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨u, rfl⟩ := α.surjective w
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz u]
  have hZinv : ∀ a ∈ Z, X * a * X⁻¹ ∈ Z := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp ha
    exact Subgroup.mem_map.mpr ⟨α z, hα_center z hz, hα_val z⟩
  have hZle : Z ≤ Q := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp ha
    exact z.2
  -- `Z(𝒬) < 𝒬` because `𝒬` is not abelian
  have hZlt : Z < Q := by
    refine lt_of_le_of_ne hZle ?_
    intro heq
    apply hnab
    rw [isMulCommutative_iff]
    intro g w
    have hg : ((g : ↥Q) : (Module.End K V)ˣ) ∈ Z := by rw [heq]; exact g.2
    obtain ⟨z, hz, hzg⟩ := Subgroup.mem_map.mp hg
    have hzg' : z = g := Subtype.ext hzg
    subst hzg'
    exact (Subgroup.mem_center_iff.mp hz w).symm
  -- by minimality `Z(𝒬)` is centralised by `X`
  have hZcomm : ∀ a ∈ Z, a * X = X * a := hmin Z hZlt hZinv
  -- Schur (L6): `Z(𝒬)` acts on `V` by scalars, since it commutes with `𝒬` and with `X`
  have hscV : ∀ z ∈ Subgroup.center ↥Q, ∃ c : K, coeRep Q z = algebraMap K (Module.End K V) c := by
    intro z hz
    have hzZ : ((z : ↥Q) : (Module.End K V)ˣ) ∈ Z := Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    have hzX : (coeRep Q z) * (X : Module.End K V) = (X : Module.End K V) * coeRep Q z := by
      simpa using congrArg (fun u : (Module.End K V)ˣ => (u : Module.End K V)) (hZcomm _ hzZ)
    have hcomm' : ∀ s ∈ ((fun a : (Module.End K V)ˣ => (a : Module.End K V)) '' (Q ∪ {X})),
        Commute (coeRep Q z) s := by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := hs
      rcases ha with haQ | haX
      · have h1 : (z : (Module.End K V)ˣ) * a = a * (z : (Module.End K V)ˣ) := by
          simpa using (congrArg (fun u : ↥Q => (u : (Module.End K V)ˣ))
            (Subgroup.mem_center_iff.mp hz ⟨a, haQ⟩)).symm
        exact congrArg (fun u : (Module.End K V)ˣ => (u : Module.End K V)) h1
      · rw [Set.mem_singleton_iff] at haX
        subst haX
        exact hzX
    obtain ⟨c, hc⟩ := exists_scalar_of_commute_irreducible
      ((fun a : (Module.End K V)ˣ => (a : Module.End K V)) '' (Q ∪ {X})) hirr (coeRep Q z) hcomm'
    exact ⟨c, hc⟩
  -- a nonzero `𝒬`-invariant submodule of minimal dimension: a `𝒬`-simple constituent `W`
  obtain ⟨W, hWne, hWinv, hWmin⟩ := exists_minimal_invariant_submodule (coeRep Q)
  haveI hWnt : Nontrivial ↥W := Submodule.nontrivial_iff_ne_bot.mpr hWne
  -- `W` is irreducible for `𝒬`
  have hWimp : Work.HallHigman.IsIrreducibleFor (Set.range (restrictRep (coeRep Q) W hWinv)) :=
    isIrreducibleFor_range_restrictRep (coeRep Q) hWinv hWne hWmin
  -- the centre still acts by scalars on `W`
  have hscW : ∀ z ∈ Subgroup.center ↥Q,
      ∃ c : K, restrictRep (coeRep Q) W hWinv z = algebraMap K (Module.End K W) c := by
    intro z hz
    obtain ⟨c, hc⟩ := hscV z hz
    exact ⟨c, restrictRep_eq_algebraMap_of_eq_smul_one (coeRep Q) W hWinv hc⟩
  -- and faithfully: an element of `Z(𝒬)` acting trivially on `W` acts trivially on all of `V`
  have hfaithW : ∀ z ∈ Subgroup.center ↥Q, restrictRep (coeRep Q) W hWinv z = 1 → z = 1 := by
    intro z hz hz1
    obtain ⟨c, hc⟩ := hscV z hz
    -- the scalar is `1`, because it acts trivially on the nonzero submodule `W`
    have hc1 : c = 1 := by
      obtain ⟨x, hxW, hx0⟩ := (Submodule.ne_bot_iff W).mp hWne
      have h2 : ((restrictRep (coeRep Q) W hWinv z) ⟨x, hxW⟩ : W) = ⟨x, hxW⟩ := by
        rw [hz1]; rfl
      have h3 : c • (x : V) = (x : V) := by
        have h4 : ((restrictRep (coeRep Q) W hWinv z) ⟨x, hxW⟩ : V) = ((⟨x, hxW⟩ : W) : V) :=
          congrArg (fun y : W => (y : V)) h2
        rw [restrictRep_apply, hc, Module.algebraMap_end_apply K K V] at h4
        simpa using h4
      have h5 : (c - 1) • (x : V) = 0 := by rw [sub_smul, one_smul, h3, sub_self]
      rcases smul_eq_zero.mp h5 with h6 | h6
      · exact sub_eq_zero.mp h6
      · exact absurd h6 hx0
    have hzV : coeRep Q z = 1 := by rw [hc, hc1, map_one]
    have hzU : (z : (Module.End K V)ˣ) = 1 := by
      refine Units.ext ?_
      simpa using hzV
    exact Subtype.ext (by simpa using hzU)
  -- the commutators of `𝒬` are central
  have hcommQ : ∀ e f' : ↥Q, e * f' * e⁻¹ * f'⁻¹ ∈ Subgroup.center ↥Q := by
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
  -- `|𝒬|` is invertible in `K`
  have hE : (Nat.card ↥Q : K) ≠ 0 := by
    intro h0
    exact h.cop ((CharP.cast_eq_zero_iff K p (Nat.card ↥Q)).mp h0)
  -- the Fourier lemma (L8) and Schur (L7) on the `𝒬`-simple module `W`
  have hL8 := fourier_finrank (restrictRep (coeRep Q) W hWinv) hscW hfaithW hcommQ hE
  have hSchur :
      Module.finrank K (Work.HallHigman.commutantOf (restrictRep (coeRep Q) W hWinv)) = 1 :=
    finrank_commutantOf_eq_one (restrictRep (coeRep Q) W hWinv) hWimp
  have hdimeq : Module.finrank K ↥W ^ 2
      = Nat.card (↥Q ⧸ Subgroup.center ↥Q) *
          Module.finrank K (Work.HallHigman.commutantOf (restrictRep (coeRep Q) W hWinv)) := by
    calc Module.finrank K ↥W ^ 2
        = Module.finrank K ↥W * Module.finrank K ↥W := by rw [pow_two]
      _ = Module.finrank K (↥W →ₗ[K] ↥W) := (Module.finrank_linearMap K K ↥W ↥W).symm
      _ = Nat.card (↥Q ⧸ Subgroup.center ↥Q) *
            Module.finrank K (Work.HallHigman.commutantOf (restrictRep (coeRep Q) W hWinv)) := hL8
  have hSsq : Nat.card (↥Q ⧸ Subgroup.center ↥Q) = Module.finrank K ↥W ^ 2 := by
    have h' := hdimeq
    rw [hSchur, mul_one] at h'
    exact h'.symm
  -- `|𝒬 / Z(𝒬)|` is odd since it divides the odd number `|𝒬|`
  have hSodd : Odd (Nat.card (↥Q ⧸ Subgroup.center ↥Q)) := by
    rw [Nat.odd_iff]
    have hoddQ : Odd (Nat.card ↥Q) := h.odd
    rw [Nat.odd_iff] at hoddQ
    obtain ⟨k, hk⟩ := Subgroup.card_quotient_dvd_card (Subgroup.center ↥Q)
    by_contra hne
    have hev : Even (Nat.card (↥Q ⧸ Subgroup.center ↥Q)) := by
      rw [Nat.even_iff]; omega
    have hevQ : Even (Nat.card ↥Q) := by
      rw [hk]
      exact hev.mul_right k
    rw [Nat.even_iff] at hevQ
    omega
  have hDodd : Odd (Module.finrank K ↥W) := by
    have h2 : Odd (Module.finrank K ↥W * Module.finrank K ↥W) := by
      have h3 : Odd (Module.finrank K ↥W ^ 2) := hSsq ▸ hSodd
      rwa [pow_two] at h3
    exact (Nat.odd_mul.mp h2).1
  -- `dim W > 1`: `dim W = 1` would make `𝒬 = Z(𝒬)` abelian
  have hD1 : 1 < Module.finrank K ↥W := by
    by_contra hcon
    have hDpos : 0 < Module.finrank K ↥W := Module.finrank_pos
    have hDeq : Module.finrank K ↥W = 1 := by omega
    have hSone : Nat.card (↥Q ⧸ Subgroup.center ↥Q) = 1 := by
      rw [hSsq, hDeq]; norm_num
    have htop : Subgroup.center ↥Q = ⊤ := by
      rw [← Subgroup.index_eq_one, Subgroup.index_eq_card]
      exact hSone
    apply hnab
    rw [isMulCommutative_iff]
    intro g w
    have hg : g ∈ Subgroup.center ↥Q := by rw [htop]; trivial
    exact (Subgroup.mem_center_iff.mp hg w).symm
  exact ⟨Module.finrank K ↥W, hDodd, hD1, hSsq.symm⟩

end Work.HallHigman.GLCore
