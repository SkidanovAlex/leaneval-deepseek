import Mathlib
import Submission.Work.FeitSibley.CharQ.Defs
import Submission.Work.FeitSibley.CharQ.prodChar_conjFun
import Submission.Work.FeitSibley.CharQ.exists_prodChar_of_mem_Irr
import Submission.Work.Frobenius.Bridge.mem_Irr_iff_coherence
import Submission.Work.Frobenius.Induced.frobenius_irr_isInduced_of_not_trivial_on_kernel
import Submission.Work.Frobenius.Induced.irr_eq_one_of_fpf
import Submission.Work.Frobenius.CharZero.mem_span_Irr_of_isClassFun
import Submission.Work.Clifford.irr_precomp_mulEquiv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.CharQ.scriptS_vanish`

Peterfalvi II, Appendice XII: every character `χ ∈ 𝒮 = {χ ∈ Irr H | Q₁ ⊄ ker χ}` vanishes
outside `Q`.

The mathematical content is the classical one (Feit–Sibley, Isaacs Thm 6.34, in the abstract
form of `Work.Frobenius.Induced.frobenius_irr_isInduced_of_not_trivial_on_kernel`): a character
of `H = Q ⋊ D` which is not trivial on `Q₁` is induced from `Q`, and an induced character
vanishes off the conjugates of the subgroup it is induced from — here that is exactly `Q`,
since `Q ⊴ H`.

Two ingredients are specific to the Feit–Sibley situation:

* the *constituent* step: some irreducible constituent `θ` of `χ|_Q` is non-trivial on `Q₁`
  (if all constituents were trivial on `Q₁`, so would be `χ`), and then
  `⟪χ, Ind_Q^H θ⟫ = ⟪χ|_Q, θ⟫ ≠ 0`;
* the *inertia* step: `D` acts fixed point freely on `Q₁`, so no `1 ≠ d ∈ D` fixes a
  `θ ∈ Irr Q` which is non-trivial on `Q₁` (`conjFun_ne_self_of_notMem_kernel`).  Writing
  `θ = prodChar lam theta` (`exists_prodChar_of_mem_Irr`), invariance under `d` forces the
  `Q₁`-component `theta` to be `d`-invariant, hence trivial
  (`Work.Frobenius.Induced.irr_eq_one_of_fpf`), contradiction.

Consequently `Ind_Q^H θ` has norm one, so it is irreducible, and pairing with `χ` shows
`χ = Ind_Q^H θ`, whence `χ x = 0` for `x ∉ Q`.

## Layout

* `mem_frobenius_Irr_of_mem_charCore_Irr` — bridge between the two vocabularies;
* `irr_eq_one_of_fpf_Q1` — a fixed-point-free `d ∈ D` fixes no non-trivial `θ ∈ Irr Q₁`;
* `exists_mem_Irr_ne_const_charPair_ne_zero` — existence of a constituent non-trivial on `A`;
* `exists_indFun_of_complement_of_inertia` — the abstract induction theorem;
* `conjFun_ne_self_of_notMem_kernel`, `conjChar_ne_self_of_notMem_kernel` — the inertia step,
  in `↥Q` and in `Q.subgroupOf H` respectively (with the transport between them);
* `isComplement'_Q_D` — `Q` and `D` are complements in `H`;
* `indFun_eq_zero_of_notMem` — an induced function vanishes off the normal subgroup;
* `scriptS_vanish` — the theorem.
-/

noncomputable section

open Classical

namespace Work.FeitSibley.CharQ

variable {G : Type} [Group G] [Fintype G]

/-! ### 1. Bridges between the vocabularies -/

/-- Every member of the core's finset of irreducible characters is an irreducible character in
the `Work.Frobenius` interface. -/
theorem mem_frobenius_Irr_of_mem_charCore_Irr {G : Type} [Group G] [Fintype G] {χ : G → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr G) : χ ∈ Work.Frobenius.Irr G :=
  (Work.Frobenius.Bridge.mem_Irr_iff_coherence).mpr
    ((Work.CharCore.mem_Irr_iff_fdrep χ).mp hχ)

/-! ### 2. A fixed-point-free element of `D` fixes no non-trivial character of `Q₁` -/

/-- **A fixed-point-free automorphism fixes no non-trivial irreducible character.**  If `θ` is an
irreducible character of `Q₁` fixed by the conjugation action of a non-trivial `d ∈ D`, then `θ`
is the trivial character. -/
theorem irr_eq_one_of_fpf_Q1 (h : Work.FeitSibley.FSData G) {d : G} (hd : d ∈ h.D)
    (hd1 : d ≠ 1) {theta : ↥h.Q1 → ℂ} (htheta : theta ∈ Work.CharCore.Irr ↥h.Q1)
    (hinv : Work.Induction.conjFun h.Q1 ⟨d, h.Q1_normal_in_H (h.D_le_H hd)⟩ theta = theta) :
    theta = fun _ : ↥h.Q1 => 1 := by
  have hF : theta ∈ Work.Frobenius.Irr ↥h.Q1 := mem_frobenius_Irr_of_mem_charCore_Irr htheta
  let σ : ↥h.Q1 →* ↥h.Q1 :=
    { toFun := fun x => ⟨d * (x : G) * d⁻¹,
        (Subgroup.mem_normalizer_iff.mp (h.Q1_normal_in_H (h.D_le_H hd)) (x : G)).mp x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hfpf : ∀ x : ↥h.Q1, σ x = x → x = 1 := by
    intro x hx
    refine Subtype.ext (h.D_fpf_Q1 d hd hd1 (x : G) x.2 ?_)
    have h2 := congrArg Subtype.val hx
    simpa [σ] using h2
  have hfix : ∀ x : ↥h.Q1, theta (σ x) = theta x := by
    intro x
    have h1 := congrFun hinv x
    rw [Work.Induction.conjFun_apply] at h1
    have h2 : Work.Induction.conjMem h.Q1 ⟨d, h.Q1_normal_in_H (h.D_le_H hd)⟩ x = σ x := by
      apply Subtype.ext
      simp [Work.Induction.conjMem_val, σ]
    rwa [h2] at h1
  exact Work.Frobenius.Induced.irr_eq_one_of_fpf σ hfpf hF hfix

/-! ### 3. A constituent of `χ|_K` which is non-trivial on `A` -/

/-- **A constituent non-trivial on `A`.**  If `f` is a class function on `K` which is not
constant on a subgroup `A ≤ K`, then some irreducible character `θ ∈ Irr K` with
`⟪f, θ⟫ ≠ 0` is non-trivial on `A`.

Indeed, write `f` as a finite linear combination `Σ_a c_a a` of irreducible characters
(`Work.Frobenius.CharZero.mem_span_Irr_of_isClassFun`); the coefficient `c_a` equals
`⟪f, a⟫` (`charPair_irr_eq_ite`), so if every `a` with `c_a ≠ 0` were trivial on `A`, then `f`
would be constant on `A`. -/
theorem exists_mem_Irr_ne_const_charPair_ne_zero {G : Type} [Group G] [Fintype G]
    {K A : Subgroup G} (hA : A ≤ K) {f : ↥K → ℂ} (hf : Work.Frobenius.IsClassFun f)
    (hne : ∃ a : ↥K, (a : G) ∈ A ∧ f a ≠ f 1) :
    ∃ θ ∈ Work.Frobenius.Irr ↥K,
      (∃ y : ↥K, (y : G) ∈ A ∧ θ y ≠ θ 1) ∧ Work.Frobenius.charPair f θ ≠ 0 := by
  classical
  obtain ⟨c, t, hts, -, hsum⟩ := Submodule.mem_span_iff_exists_finset_subset.mp
    (Work.Frobenius.CharZero.mem_span_Irr_of_isClassFun hf)
  have hca : ∀ a ∈ t, Work.Frobenius.charPair f a = c a := by
    intro a ha
    rw [← hsum, Work.Frobenius.charPair_sum_smul_left]
    have hsingle : (∑ b ∈ t, c b * Work.Frobenius.charPair b a)
        = c a * Work.Frobenius.charPair a a := by
      refine Finset.sum_eq_single a ?_ ?_
      · intro b hb hba
        rw [Work.Frobenius.Irr.charPair_irr_eq_ite (hts hb) (hts ha), ite_eq_right hba,
          mul_zero]
      · intro hnot
        exact absurd ha hnot
    rw [hsingle, Work.Frobenius.Irr.charPair_irr_eq_ite (hts ha) (hts ha), ite_eq_left rfl,
      mul_one]
  by_contra hcon
  push_neg at hcon
  have htriv : ∀ a ∈ t, c a ≠ 0 → ∀ y : ↥K, (y : G) ∈ A → a y = a 1 := by
    intro a ha hc0 y hyA
    by_contra hane
    have h1 : Work.Frobenius.charPair f a = 0 := hcon a (hts ha) ⟨y, hyA, hane⟩
    rw [hca a ha] at h1
    exact hc0 h1
  obtain ⟨a₀, ha₀A, ha₀ne⟩ := hne
  have hfun : ∀ y : ↥K, f y = ∑ a ∈ t, c a * a y := by
    intro y
    rw [← hsum]
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hmain : f a₀ = f 1 := by
    calc f a₀ = ∑ a ∈ t, c a * a a₀ := hfun a₀
      _ = ∑ a ∈ t, c a * a 1 := by
          refine Finset.sum_congr rfl fun a ha => ?_
          by_cases hc0 : c a = 0
          · rw [hc0, zero_mul, zero_mul]
          · rw [htriv a ha hc0 a₀ ha₀A]
      _ = f 1 := (hfun 1).symm
  exact ha₀ne hmain

/-! ### 4. The abstract induction theorem -/

/-- **A character non-trivial on `A ≤ K` is induced from `K`**, in the situation where `K ⊴ G`
has a complement `He` (so `G = K ⋊ He`) acting on `Irr K` with trivial stabilisers on the
characters non-trivial on `A`.

This is `Work.Frobenius.Induced.frobenius_irr_isInduced_of_not_trivial_on_kernel` with the
Frobenius hypotheses replaced by the two abstract inputs `hcomp` and `hinertia`. -/
theorem exists_indFun_of_complement_of_inertia {G : Type} [Group G] [Fintype G]
    {K He A : Subgroup G} [K.Normal] (hcomp : Subgroup.IsComplement' K He) (hA : A ≤ K)
    (hinertia : ∀ θ : ↥K → ℂ, θ ∈ Work.Frobenius.Irr ↥K →
      (∃ y : ↥K, (y : G) ∈ A ∧ θ y ≠ θ 1) →
      ∀ h : G, h ∈ He → h ≠ 1 → Work.Frobenius.Induced.conjChar K h θ ≠ θ)
    {χ : G → ℂ} (hχ : χ ∈ Work.Frobenius.Irr G)
    (hker : ∃ x : G, x ∈ A ∧ χ x ≠ χ 1) :
    ∃ θ : ↥K → ℂ, θ ∈ Work.Frobenius.Irr ↥K ∧
      (∃ y : ↥K, (y : G) ∈ A ∧ θ y ≠ θ 1) ∧
      χ = Work.Frobenius.indFun K θ := by
  classical
  have hfcf : Work.Frobenius.IsClassFun (Work.Frobenius.resFun K χ) :=
    Work.Frobenius.Induced.isClassFun_resFun (Work.Frobenius.irr_isClassFun hχ)
  obtain ⟨x₀, hx₀A, hx₀ne⟩ := hker
  have hfne : ∃ a : ↥K, (a : G) ∈ A ∧ Work.Frobenius.resFun K χ a ≠ Work.Frobenius.resFun K χ 1 :=
    ⟨⟨x₀, hA hx₀A⟩, hx₀A, by simpa [Work.Frobenius.resFun] using hx₀ne⟩
  obtain ⟨θ, hθ, hθA, hpair⟩ := exists_mem_Irr_ne_const_charPair_ne_zero hA hfcf hfne
  refine ⟨θ, hθ, hθA, ?_⟩
  -- Frobenius reciprocity
  have hrec : Work.Frobenius.charPair χ (Work.Frobenius.indFun K θ)
      = Work.Frobenius.charPair θ (Work.Frobenius.resFun K χ) := by
    rw [Work.Frobenius.charPair_comm,
      Work.Frobenius.Induction.charPair_indFun_resFun (φ := θ) (ψ := χ)
        (Work.Frobenius.irr_isClassFun hχ)]
  have hpairχ : Work.Frobenius.charPair χ (Work.Frobenius.indFun K θ) ≠ 0 := by
    rw [hrec, Work.Frobenius.charPair_comm]
    exact hpair
  -- the induced character has norm one
  have hnorm : Work.Frobenius.charPair (Work.Frobenius.indFun K θ) (Work.Frobenius.indFun K θ)
      = 1 := by
    rw [Work.Frobenius.Induction.charPair_indFun_resFun (φ := θ)
      (ψ := Work.Frobenius.indFun K θ) (Work.Frobenius.Induction.isClassFun_indFun θ)]
    rw [Work.Frobenius.Induced.resFun_indFun_eq_sum_conjChar hcomp
      (Work.Frobenius.irr_isClassFun hθ)]
    rw [Work.Frobenius.charPair_sum_right]
    trans ∑ h : ↥He, (if θ = Work.Frobenius.Induced.conjChar K (h : G) θ then 1 else 0)
    · exact Finset.sum_congr rfl fun h _ =>
        Work.Frobenius.Irr.charPair_irr_eq_ite hθ
          (Work.Frobenius.Induced.conjChar_mem_Irr (h : G) hθ)
    · rw [Finset.sum_eq_single (1 : ↥He)]
      · simp
      · intro h _ hh1
        exact ite_eq_right fun hcontra =>
          hinertia θ hθ hθA (h : G) h.2 (fun hc => hh1 (Subtype.ext hc)) hcontra.symm
      · intro hnot
        exact absurd (Finset.mem_univ (1 : ↥He)) hnot
  have hV : Work.Frobenius.IsVChar (Work.Frobenius.indFun K θ) :=
    Work.Frobenius.isVChar_indFun (AddSubgroup.subset_closure hθ)
  obtain ⟨χ', hχ', hcase⟩ := Work.Frobenius.VChar.vchar_norm_one hV hnorm
  rcases hcase with h | h
  · -- `Ind_K^G θ = χ'`, and the non-zero pairing with `χ` forces `χ = χ'`
    rw [h] at hpairχ
    have hχχ' : χ = χ' := by
      by_contra hne
      rw [Work.Frobenius.Irr.charPair_irr_eq_ite hχ hχ', ite_eq_right hne] at hpairχ
      exact hpairχ rfl
    exact hχχ'.trans h.symm
  · -- the negative case is excluded by positivity of the degree
    exfalso
    obtain ⟨m, hmpos, hm⟩ := Work.Frobenius.character_one_eq_natCast hχ'
    obtain ⟨n, hnpos, hn⟩ := Work.Frobenius.character_one_eq_natCast hθ
    have h1 := congrFun h 1
    rw [Work.Frobenius.Induced.indFun_apply_one_eq K θ, hn, Pi.neg_apply, hm] at h1
    have h2 : ((K.index * n + m : ℕ) : ℂ) = 0 := by
      push_cast
      rw [h1]
      ring
    have h3 : K.index * n + m = 0 := by exact_mod_cast h2
    omega

/-! ### 5. The inertia step in `↥Q` -/

/-- **No `1 ≠ d ∈ D` fixes a `φ ∈ Irr Q` which is non-trivial on `Q₁`.**

Write `φ = prodChar lam theta` with `lam ∈ Irr S`, `theta ∈ Irr Q₁`
(`Work.FeitSibley.CharQ.exists_prodChar_of_mem_Irr`).  If `d` fixes `φ`, then — evaluating the
identity `φ^d = φ` at the elements `prodIso (1, b)` (`b ∈ Q₁`) and using that `d` acts
componentwise on `S × Q₁` (`prodChar_conjFun`) — the character `theta` is `d`-invariant, hence
trivial (`irr_eq_one_of_fpf_Q1`); but `φ` non-trivial on `Q₁` means `theta` is non-trivial. -/
theorem conjFun_ne_self_of_notMem_kernel (h : Work.FeitSibley.FSData G) {phi : ↥h.Q → ℂ}
    (hphi : phi ∈ Work.CharCore.Irr ↥h.Q)
    (hQ1 : ∃ x : ↥h.Q, (x : G) ∈ h.Q1 ∧ phi x ≠ phi 1)
    {d : G} (hd : d ∈ h.D) (hd1 : d ≠ 1) :
    Work.Induction.conjFun h.Q ⟨d, h.Q_normal_in_H (h.D_le_H hd)⟩ phi ≠ phi := by
  intro hconj
  obtain ⟨lam, hlam, theta, htheta, hphi_eq⟩ :=
    Work.FeitSibley.CharQ.exists_prodChar_of_mem_Irr h hphi
  subst hphi_eq
  have hlam1 : lam 1 ≠ 0 := by
    rw [Work.CharCore.irrDeg_spec hlam]
    simp only [ne_eq, Nat.cast_eq_zero]
    exact (Work.CharCore.irrDeg_pos hlam).ne'
  -- `theta` is not the trivial character
  have htheta_ne : theta ≠ fun _ : ↥h.Q1 => 1 := by
    intro htheta1
    obtain ⟨x, hxQ1, hxne⟩ := hQ1
    have hx : h.prodIso ((1 : ↥h.S), (⟨(x : G), hxQ1⟩ : ↥h.Q1)) = x := by
      apply Subtype.ext
      simp [Work.FeitSibley.FSData.prodIso_apply, Work.FeitSibley.FSData.prodHom_apply]
    have h1 : h.prodIso ((1 : ↥h.S), (1 : ↥h.Q1)) = (1 : ↥h.Q) := by
      apply Subtype.ext
      simp [Work.FeitSibley.FSData.prodIso_apply, Work.FeitSibley.FSData.prodHom_apply]
    have hxe : h.prodChar lam theta x = lam 1 := by
      rw [← hx, h.prodChar_apply, htheta1]
      simp
    have h1e : h.prodChar lam theta 1 = lam 1 := by
      rw [← h1, h.prodChar_apply, htheta1]
      simp
    rw [hxe, h1e] at hxne
    exact hxne rfl
  -- `theta` is fixed by `d`
  have htheta_fix :
      Work.Induction.conjFun h.Q1 ⟨d, h.Q1_normal_in_H (h.D_le_H hd)⟩ theta = theta := by
    funext b
    rw [Work.Induction.conjFun_apply]
    have h1 := congrFun hconj (h.prodIso ((1 : ↥h.S), b))
    rw [Work.FeitSibley.CharQ.prodChar_conjFun h d hd lam theta] at h1
    rw [h.prodChar_apply, h.prodChar_apply, Work.Induction.conjFun_apply,
      Work.Induction.conjFun_apply] at h1
    have hS1 : Work.Induction.conjMem h.S ⟨d, h.S_normal_in_H (h.D_le_H hd)⟩ (1 : ↥h.S) = 1 :=
      Subtype.ext (by simp)
    rw [hS1] at h1
    exact mul_left_cancel₀ hlam1 h1
  exact htheta_ne (irr_eq_one_of_fpf_Q1 h hd hd1 htheta htheta_fix)

/-! ### 6. The inertia step for the subgroup `Q.subgroupOf H` -/

/-- **No `1 ≠ d ∈ D` fixes a `θ ∈ Irr (Q.subgroupOf H)` which is non-trivial on `Q₁`.**

This is `conjFun_ne_self_of_notMem_kernel`, transported from `↥Q` to the subgroup
`Q.subgroupOf H` of `↥H` along the canonical isomorphism `e : Q.subgroupOf H ≃* Q` (which is the
identity on the underlying elements of `G`). -/
theorem conjChar_ne_self_of_notMem_kernel (h : Work.FeitSibley.FSData G)
    [hQn : (h.Q.subgroupOf h.H).Normal]
    {theta : ↥(h.Q.subgroupOf h.H) → ℂ}
    (htheta : theta ∈ Work.Frobenius.Irr ↥(h.Q.subgroupOf h.H))
    (hQ1 : ∃ y : ↥(h.Q.subgroupOf h.H), ((y : ↥h.H) : G) ∈ h.Q1 ∧ theta y ≠ theta 1)
    {d : ↥h.H} (hd : d ∈ h.D.subgroupOf h.H) (hd1 : d ≠ 1) :
    Work.Frobenius.Induced.conjChar (h.Q.subgroupOf h.H) d theta ≠ theta := by
  intro hfix
  -- the transport isomorphism
  let e : ↥(h.Q.subgroupOf h.H) ≃* ↥h.Q :=
    { toFun := fun y => ⟨(y : G), y.2⟩
      invFun := fun q => ⟨⟨(q : G), h.Q_le_H q.2⟩, q.2⟩
      left_inv := fun y => Subtype.ext rfl
      right_inv := fun q => Subtype.ext rfl
      map_mul' := fun y z => Subtype.ext rfl }
  let phi : ↥h.Q → ℂ := fun q => theta (e.symm q)
  have hphi : phi ∈ Work.CharCore.Irr ↥h.Q := by
    have h1 : theta ∈ Work.Coherence.Irr ↥(h.Q.subgroupOf h.H) :=
      (Work.Frobenius.Bridge.mem_Irr_iff_coherence).mp htheta
    have h2 : theta ∈ Work.Clifford.Irr ↥(h.Q.subgroupOf h.H) :=
      (Work.Clifford.mem_Irr_iff_coherence).mpr h1
    have h3 : phi ∈ Work.Clifford.Irr ↥h.Q := Work.Clifford.irr_precomp_mulEquiv e.symm h2
    exact (Work.CharCore.mem_Irr_iff_coherence).mpr
      ((Work.Clifford.mem_Irr_iff_coherence).mp h3)
  have hQ1' : ∃ x : ↥h.Q, (x : G) ∈ h.Q1 ∧ phi x ≠ phi 1 := by
    obtain ⟨y, hyQ1, hyne⟩ := hQ1
    refine ⟨e y, ?_, ?_⟩
    · change ((y : ↥h.H) : G) ∈ h.Q1
      exact hyQ1
    have h1 : phi (e y) = theta y := by
      change theta (e.symm (e y)) = theta y
      rw [MulEquiv.symm_apply_apply]
    have h2 : phi 1 = theta 1 := by
      change theta (e.symm 1) = theta 1
      rw [map_one]
    rw [h1, h2]
    exact hyne
  -- transport of the invariance
  have hconj : Work.Induction.conjFun h.Q ⟨(d : G), h.Q_normal_in_H (h.D_le_H hd)⟩ phi = phi := by
    funext q
    rw [Work.Induction.conjFun_apply]
    obtain ⟨z, rfl⟩ : ∃ z : ↥(h.Q.subgroupOf h.H), e z = q :=
      ⟨e.symm q, MulEquiv.apply_symm_apply e q⟩
    have hze : phi (e z) = theta z := by
      change theta (e.symm (e z)) = theta z
      rw [MulEquiv.symm_apply_apply]
    -- the conjugate element of `Q.subgroupOf H`
    have hmem : ((d : ↥h.H) * (z : ↥h.H) * (d : ↥h.H)⁻¹ : G) ∈ h.Q := by
      have hdH : ((d : ↥h.H) : G) ∈ Subgroup.normalizer (h.Q : Set G) :=
        h.Q_normal_in_H (d : ↥h.H).2
      have h1 := (Subgroup.mem_normalizer_iff.mp hdH ((z : ↥h.H) : G)).mp z.2
      simpa using h1
    have hmem' : (d : ↥h.H) * (z : ↥h.H) * (d : ↥h.H)⁻¹ ∈ h.Q.subgroupOf h.H := hmem
    have hkey : Work.Induction.conjMem h.Q ⟨(d : G), h.Q_normal_in_H (h.D_le_H hd)⟩ (e z) =
        e (⟨(d : ↥h.H) * (z : ↥h.H) * (d : ↥h.H)⁻¹, hmem'⟩ :
          ↥(h.Q.subgroupOf h.H)) := by
      apply Subtype.ext
      simp [Work.Induction.conjMem_val, hmem', e]
    rw [hkey, hze]
    have hze2 : phi (e (⟨(d : ↥h.H) * (z : ↥h.H) * (d : ↥h.H)⁻¹, hmem'⟩ :
        ↥(h.Q.subgroupOf h.H)))
        = theta (⟨(d : ↥h.H) * (z : ↥h.H) * (d : ↥h.H)⁻¹, hmem'⟩ :
            ↥(h.Q.subgroupOf h.H)) := by
      change theta (e.symm (e _)) = theta _
      rw [MulEquiv.symm_apply_apply]
    rw [hze2]
    have hz := congrFun hfix z
    rw [Work.Frobenius.Induced.conjChar_apply] at hz
    have hEq : (⟨(d : ↥h.H) * (z : ↥h.H) * (d : ↥h.H)⁻¹, hmem'⟩ :
          ↥(h.Q.subgroupOf h.H)) =
        (⟨(d : ↥h.H) * (z : ↥h.H) * (d : ↥h.H)⁻¹,
          (inferInstance : (h.Q.subgroupOf h.H).Normal).conj_mem (z : ↥h.H) z.2 d⟩ :
          ↥(h.Q.subgroupOf h.H)) := Subtype.ext rfl
    rw [← hEq]
    exact hz
  exact conjFun_ne_self_of_notMem_kernel h hphi hQ1' hd
    (fun hc => hd1 (Subtype.ext hc)) hconj

/-! ### 7. `Q` and `D` are complements in `H` -/

/-- The subgroups `Q` and `D` of `H = Q ⋊ D`, viewed inside `↥H`, are complements. -/
theorem isComplement'_Q_D (h : Work.FeitSibley.FSData G) :
    Subgroup.IsComplement' (h.Q.subgroupOf h.H) (h.D.subgroupOf h.H) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    intro y hy
    obtain ⟨hyQ, hyD⟩ := Subgroup.mem_inf.mp hy
    have hy' : (y : G) ∈ h.Q ⊓ h.D := Subgroup.mem_inf.mpr ⟨hyQ, hyD⟩
    rw [h.Q_inf_D] at hy'
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hy'))
  · ext y
    constructor
    · intro _
      exact Set.mem_univ y
    · intro _
      obtain ⟨q, hq, d, hd, hqd⟩ := h.mem_H_decomp y.2
      refine Set.mem_mul.mpr ⟨⟨q, h.Q_le_H hq⟩, hq, ⟨d, h.D_le_H hd⟩, hd, ?_⟩
      exact Subtype.ext hqd.symm

/-! ### 8. An induced function vanishes off its normal subgroup -/

/-- A function induced from a normal subgroup `K ⊴ G` vanishes off `K`: every conjugate of
`x ∉ K` lies outside `K`, so all terms of the defining sum of `indFun` vanish. -/
theorem indFun_eq_zero_of_notMem {G : Type} [Group G] [Fintype G] {K : Subgroup G} [K.Normal]
    (θ : ↥K → ℂ) {x : G} (hx : x ∉ K) : Work.Frobenius.indFun K θ x = 0 := by
  have hval : Work.Frobenius.indFun K θ x =
      (Nat.card K : ℂ)⁻¹ *
        ∑ y : G, (if hy : y * x * y⁻¹ ∈ K then θ ⟨y * x * y⁻¹, hy⟩ else 0) := rfl
  rw [hval, mul_eq_zero]
  right
  refine Finset.sum_eq_zero fun y _ => ?_
  by_cases hy : y * x * y⁻¹ ∈ K
  · refine absurd ?_ hx
    have h1 : x = y⁻¹ * (y * x * y⁻¹) * y := by group
    rw [h1]
    simpa using (inferInstance : K.Normal).conj_mem (y * x * y⁻¹) hy y⁻¹
  · simp [hy]

/-! ### 9. The theorem -/

theorem scriptS_vanish {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {chi : ↥h.H → ℂ} (hchi : chi ∈ Work.FeitSibley.scriptS h.H h.Q1)
    {x : ↥h.H} (hx : (x : G) ∉ h.Q) : chi x = 0 := by
  classical
  -- `Work.CharCore.Irr` (and hence `𝒮`) was elaborated in the blueprint with the standard
  -- `Subtype` `Fintype` instance for `↥H`; align the instance used here with it.
  letI : Fintype ↥h.H := h.H.instFintypeSubtypeMemOfDecidablePred
  have hchi' : chi ∈ Work.CharCore.Irr ↥h.H ∧
      ∃ y : ↥h.H, (y : G) ∈ h.Q1 ∧ chi y ≠ chi 1 := by
    have h := hchi
    simp only [Submission.Blueprint.excludingKernel, Finset.mem_filter] at h
    exact h
  obtain ⟨hchiIrr, x₀, hx₀Q1, hx₀ne⟩ := hchi'
  haveI hQn : (h.Q.subgroupOf h.H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer h.Q_normal_in_H
  have hcomp : Subgroup.IsComplement' (h.Q.subgroupOf h.H) (h.D.subgroupOf h.H) :=
    isComplement'_Q_D h
  have hAle : h.Q1.subgroupOf h.H ≤ h.Q.subgroupOf h.H :=
    Subgroup.subgroupOf_mono h.H h.Q1_le_Q
  have hFchi : chi ∈ Work.Frobenius.Irr ↥h.H :=
    mem_frobenius_Irr_of_mem_charCore_Irr hchiIrr
  have hker' : ∃ y : ↥h.H, y ∈ h.Q1.subgroupOf h.H ∧ chi y ≠ chi 1 :=
    ⟨x₀, hx₀Q1, hx₀ne⟩
  obtain ⟨theta, -, -, hchi_eq⟩ :=
    exists_indFun_of_complement_of_inertia (G := ↥h.H) (K := h.Q.subgroupOf h.H)
      (He := h.D.subgroupOf h.H) (A := h.Q1.subgroupOf h.H) hcomp hAle
      (fun θ hθ hθA d hd hd1 => conjChar_ne_self_of_notMem_kernel h hθ hθA hd hd1)
      hFchi hker'
  have hxK : x ∉ h.Q.subgroupOf h.H := hx
  rw [hchi_eq]
  exact indFun_eq_zero_of_notMem theta hxK

end Work.FeitSibley.CharQ
