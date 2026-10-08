import Mathlib
import Submission.Work.CharPrelim.Defs
import Submission.Work.CharPrelim.indFun_eq_smul_sum_image

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharPrelim.ft4_5_aux`: helpers shared by the FT 4.5 development

Small reusable lemmas about `Work.CharCore.cfInner`, `Work.Induction.indFun`, irreducible
characters, and commutative quotients, extracted from `ft4_5.lean` so that the auxiliary
lemmas of the Hall case (extension of an invariant irreducible character across a
coprime abelian quotient) can use them without importing the target file.
-/

namespace Work.CharPrelim

open Classical

/-- An induced function from a normal subgroup vanishes off that subgroup. -/
theorem indFun_eq_zero_of_notMem {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    (φ : ↥N → ℂ) {x : G} (hx : x ∉ N) : Work.Induction.indFun N φ x = 0 :=
  Work.Induction.indFun_apply_eq_zero N φ x fun y hy => hx (by
    have h1 := (inferInstance : N.Normal).conj_mem (y * x * y⁻¹) hy y⁻¹
    rw [inv_inv] at h1
    rwa [show y⁻¹ * (y * x * y⁻¹) * y = x from by group] at h1)

/-- For a normal subgroup `N` with commutative quotient, the number of irreducible characters of
the quotient is the index of `N`, hence `∑_{β ∈ Irr (G ⧸ N)} β 1 = [G : N]`. -/
theorem sum_irr_one_eq_index {G : Type*} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    [Fintype (G ⧸ N)] [IsMulCommutative (G ⧸ N)] :
    ∑ β ∈ Work.CharCore.Irr (G ⧸ N), β 1 = (N.index : ℂ) := by
  classical
  have h1 : ∀ β ∈ Work.CharCore.Irr (G ⧸ N), β 1 = 1 := by
    intro β hβ
    rw [Work.CharCore.irrDeg_spec hβ, Work.CharCore.irrDeg_eq_one_of_commutative hβ]
    norm_num
  have h2 : ((Work.CharCore.Irr (G ⧸ N)).card : ℂ) = (Nat.card (G ⧸ N) : ℂ) := by
    have h3 : ∑ β ∈ Work.CharCore.Irr (G ⧸ N), β 1 ^ 2
        = ((Work.CharCore.Irr (G ⧸ N)).card : ℂ) := by
      calc ∑ β ∈ Work.CharCore.Irr (G ⧸ N), β 1 ^ 2
          = ∑ _β ∈ Work.CharCore.Irr (G ⧸ N), (1 : ℂ) :=
            Finset.sum_congr rfl (fun β hβ => by rw [h1 β hβ]; norm_num)
        _ = ((Work.CharCore.Irr (G ⧸ N)).card : ℂ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [← h3, Work.CharCore.sum_irr_degree_sq]
  calc ∑ β ∈ Work.CharCore.Irr (G ⧸ N), β 1
      = ∑ _β ∈ Work.CharCore.Irr (G ⧸ N), (1 : ℂ) :=
        Finset.sum_congr rfl h1
    _ = ((Work.CharCore.Irr (G ⧸ N)).card : ℂ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (N.index : ℂ) := by rw [h2, ← Subgroup.index_eq_card]

/-- If a class function is a nonzero multiple of a sum of distinct irreducible characters, then
its support (the irreducibles with nonzero inner product against it) is exactly that finset. -/
theorem support_of_eq_smul_sum {G : Type*} [Group G] [Fintype G] {c : ℂ} (hc : c ≠ 0)
    {S : Finset (G → ℂ)} (hS : ∀ χ ∈ S, χ ∈ Work.CharCore.Irr G) {F : G → ℂ}
    (hF : F = c • ∑ χ ∈ S, χ) :
    ∀ χ ∈ Work.CharCore.Irr G, (χ ∈ S ↔ Work.CharCore.cfInner F χ ≠ 0) := by
  intro χ hχ
  have hkey : Work.CharCore.cfInner F χ = c * (if χ ∈ S then (1 : ℂ) else 0) := by
    rw [hF, Work.CharCore.cfInner_smul_left, Work.CharCore.cfInner_sum_left]
    congr 1
    rw [Finset.sum_congr rfl (fun χ' hχ' => Work.CharCore.irr_orthonormal χ' χ (hS χ' hχ') hχ)]
    exact Finset.sum_ite_eq' S χ (fun _ => (1 : ℂ))
  rw [hkey]
  constructor
  · intro h
    rw [ite_eq_left h]
    exact mul_ne_zero hc one_ne_zero
  · intro h
    by_contra hnot
    rw [ite_eq_right hnot, mul_zero] at h
    exact h rfl

/-- The quotient of a subgroup `I` of `X₀` by `H.subgroupOf I` is commutative as soon as
`⁅X₀, X₀⁆ ≤ H` and `I ≤ X₀`. -/
theorem isMulCommutative_quotient_subgroupOf {X : Type*} [Group X] {H X₀ I : Subgroup X}
    [H.Normal] (hIX₀ : I ≤ X₀) (hab : ⁅X₀, X₀⁆ ≤ H) :
    IsMulCommutative (↥I ⧸ H.subgroupOf I) := by
  refine ⟨⟨fun x y => ?_⟩⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (H.subgroupOf I) x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (H.subgroupOf I) y
  simp only [QuotientGroup.mk'_apply]
  have hmem : ((a * b) * (b * a)⁻¹ : ↥I) ∈ H.subgroupOf I := by
    rw [Subgroup.mem_subgroupOf]
    have h2 : (↑((a * b) * (b * a)⁻¹) : X) =
        (↑a : X) * (↑b : X) * ((↑a : X))⁻¹ * ((↑b : X))⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h2]
    simpa only [commutatorElement_def] using
      (Subgroup.commutator_le.mp hab) (↑a : X) (hIX₀ a.2) (↑b : X) (hIX₀ b.2)
  have hx : (↑(((a * b) * (b * a)⁻¹) : ↥I) : ↥I ⧸ H.subgroupOf I) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hmem
  have h3 : ((↑(a * b) : ↥I ⧸ H.subgroupOf I)) = (↑(b * a) : ↥I ⧸ H.subgroupOf I) := by
    simpa only [map_mul, map_inv, mul_inv_rev, inv_inv] using mul_inv_eq_one.mp hx
  simpa only [QuotientGroup.mk_mul] using h3

/-- A sum over the subtype of a filtered finset equals the sum over the ambient finset when the
summand vanishes away from the filter. -/
theorem sum_subtype_eq_sum_of_eq_zero_off {ι : Type*} {M : Type*} [AddCommMonoid M]
    (s : Finset ι) (p : ι → Prop) [DecidablePred p] (f : ι → M)
    (h0 : ∀ x ∈ s, ¬ p x → f x = 0) :
    (s.filter p).attach.sum (fun x => f x) = s.sum f := by
  rw [Finset.sum_attach, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x hx => ?_
  by_cases h : p x
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, h0 x hx h]

/-- The inner product on a finite type does not depend on the `Fintype` instance (needed because
`Work.CharCore.cfInner` on a subgroup is used with two syntactically different instances). -/
theorem cfInner_inst_eq {G : Type*} (i₁ i₂ : Fintype G) (f g : G → ℂ) :
    @Work.CharCore.cfInner G i₁ f g = @Work.CharCore.cfInner G i₂ f g := by
  have hcard : @Fintype.card G i₁ = @Fintype.card G i₂ := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  have huniv : (@Finset.univ G i₁) = (@Finset.univ G i₂) := Finset.ext fun x => by simp
  unfold Work.CharCore.cfInner
  rw [hcard, huniv]

/-- Every irreducible character of a subgroup `N` is a constituent of the restriction of some
irreducible character of the ambient group. -/
theorem exists_irr_constituent_indFun {G : Type*} [Group G] [Fintype G] {N : Subgroup G}
    [instN : Fintype ↥N] {θ : ↥N → ℂ} (hθ : θ ∈ Work.CharCore.Irr ↥N) :
    ∃ lam ∈ Work.CharCore.Irr G, Work.CharCore.cfInner θ (Work.Induction.resFun N lam) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hzero : Work.Induction.indFun N θ = 0 := by
    rw [Work.CharCore.classFun_eq_sum_irr (Work.Induction.isClassFun_indFun N θ)]
    refine Finset.sum_eq_zero fun χ hχ => ?_
    have h : Work.CharCore.cfInner (Work.Induction.indFun N θ) χ = 0 := by
      rw [Work.Induction.frobenius_reciprocity N θ χ (Work.CharCore.isClassFun_of_mem_Irr hχ),
        cfInner_inst_eq (i₁ := N.instFintypeSubtypeMemOfDecidablePred) (i₂ := instN)
          θ (Work.Induction.resFun N χ)]
      exact hcon χ hχ
    rw [h, zero_smul]
  have h1 : Work.Induction.indFun N θ 1 = (N.index : ℂ) * θ 1 :=
    Work.Induction.indFun_apply_one N θ
  rw [hzero] at h1
  simp only [Pi.zero_apply] at h1
  have hne : ((N.index : ℂ) * θ 1) ≠ 0 := by
    refine mul_ne_zero (Nat.cast_ne_zero.mpr (Subgroup.index_ne_zero_of_finite)) ?_
    rw [Work.CharCore.irrDeg_spec hθ]
    exact Work.CharCore.irrDeg_ne_zero hθ
  exact hne h1.symm

/-- Elementary arithmetic: if `∑ n i = |s| * c` and `∑ (n i)^2 = |s| * c^2`, then all the
natural numbers `n i` equal `c`. -/
theorem nat_eq_of_sum_eq_of_sum_sq_eq {ι : Type*} (s : Finset ι) (n : ι → ℕ) {c : ℕ}
    (h1 : ∑ i ∈ s, n i = s.card * c) (h2 : ∑ i ∈ s, n i ^ 2 = s.card * c ^ 2) :
    ∀ i ∈ s, n i = c := by
  have hcast1 : (∑ i ∈ s, (n i : ℤ)) = s.card * c := by exact_mod_cast h1
  have hcast2 : (∑ i ∈ s, (n i : ℤ) ^ 2) = s.card * c ^ 2 := by exact_mod_cast h2
  have h3 : ∑ i ∈ s, ((n i : ℤ) - c) ^ 2 = 0 := by
    have hexp : ∀ i : ι, ((n i : ℤ) - c) ^ 2 = (n i : ℤ) ^ 2 - 2 * c * (n i : ℤ) + c ^ 2 := by
      intro i; ring
    rw [Finset.sum_congr rfl (fun i _ => hexp i)]
    have hA : ∑ i ∈ s, (2 * c * (n i : ℤ)) = 2 * c * (s.card * c) := by
      rw [← Finset.mul_sum, hcast1]
    have hB : ∑ i ∈ s, (c ^ 2 : ℤ) = s.card * c ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hcast2, hA, hB]
    ring
  have h4 : ∀ i ∈ s, ((n i : ℤ) - c) ^ 2 = 0 := fun i hi =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp h3 i hi
  intro i hi
  have h5 : (n i : ℤ) = c := by
    have := h4 i hi
    nlinarith [sq_nonneg ((n i : ℤ) - c)]
  exact_mod_cast h5

open Classical in
/-- (FT 4.5, Hall case, pair form.)  Let `N ⊴ G` with `G ⧸ N` commutative and `θ ∈ Irr N` of full
inertia.  If `θ` extends to an irreducible character of `G`, then `Ind_N^G θ` is a sum of `N.index`
distinct irreducible characters of `G`, all of degree `irrDeg θ`.

The extension hypothesis is the conclusion of `Work.CharPrelim.exists_extension_of_coprime`
(Glauberman's extension theorem in the coprime abelian-quotient case); everything else here is the
"M-trick" `indFun_eq_smul_sum_image` plus the observation that the extension has multiplicity one. -/
theorem exists_sum_of_extension {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    [Fintype ↥N] [Fintype (G ⧸ N)] {θ : ↥N → ℂ} (hθ : θ ∈ Work.CharCore.Irr ↥N)
    (hinv : Work.Clifford.inertia N θ = ⊤) [IsMulCommutative (G ⧸ N)]
    (hext : ∃ lam ∈ Work.CharCore.Irr G, Work.Induction.resFun N lam = θ) :
    ∃ T : Finset (G → ℂ), (∀ χ ∈ T, χ ∈ Work.CharCore.Irr G) ∧ T.card = N.index ∧
      (∀ χ ∈ T, Work.CharCore.irrDeg χ = Work.CharCore.irrDeg θ) ∧
      Work.Induction.indFun N θ = ∑ χ ∈ T, χ := by
  classical
  obtain ⟨lam, hlam, hres⟩ := hext
  have hlamθ : Work.CharCore.cfInner θ (Work.Induction.resFun N lam) ≠ 0 := by
    rw [hres, Work.CharCore.irr_orthonormal θ θ hθ hθ]
    norm_num
  obtain ⟨e, he, hreslam, hdeg, hid⟩ :=
    indFun_eq_smul_sum_image (N := N) hθ hinv hlam hlamθ
  have hθ1 : θ 1 ≠ 0 := by
    rw [Work.CharCore.irrDeg_spec hθ]
    exact Work.CharCore.irrDeg_ne_zero hθ
  -- the extension has multiplicity one
  have he1 : (e : ℂ) = 1 := by
    have hfun : (e : ℂ) • θ = θ := by rw [← hreslam, hres]
    have hfun1 : (e : ℂ) * θ 1 = θ 1 := by
      have h1 := congrFun hfun (1 : ↥N)
      simpa only [Pi.smul_apply, smul_eq_mul] using h1
    have h1 : (e : ℂ) * θ 1 = 1 * θ 1 := by rw [one_mul]; exact hfun1
    exact mul_right_cancel₀ hθ1 h1
  have hlam1 : lam 1 = θ 1 := by
    simpa using congrFun hres (1 : ↥N)
  have hdegLam : Work.CharCore.irrDeg lam = Work.CharCore.irrDeg θ := by
    have h2 : (Work.CharCore.irrDeg lam : ℂ) = (Work.CharCore.irrDeg θ : ℂ) := by
      rw [← Work.CharCore.irrDeg_spec hlam, ← Work.CharCore.irrDeg_spec hθ, hlam1]
    exact_mod_cast h2
  refine ⟨(Work.CharCore.Irr (G ⧸ N)).image
    (fun β => lam * Work.Clifford.inflateFun N β), ?_, ?_, ?_, ?_⟩
  · intro χ hχ
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hχ
    exact (hdeg β hβ).1
  · -- the number of constituents is the index
    have h1 : Work.Induction.indFun N θ 1 = (N.index : ℂ) * θ 1 :=
      Work.Induction.indFun_apply_one N θ
    have h2 : (∑ χ ∈ (Work.CharCore.Irr (G ⧸ N)).image
        (fun β => lam * Work.Clifford.inflateFun N β), χ) 1
        = (((Work.CharCore.Irr (G ⧸ N)).image
            (fun β => lam * Work.Clifford.inflateFun N β)).card : ℂ) * θ 1 := by
      rw [Finset.sum_apply]
      have h3 : ∀ χ ∈ (Work.CharCore.Irr (G ⧸ N)).image
          (fun β => lam * Work.Clifford.inflateFun N β), χ 1 = θ 1 := by
        intro χ hχ
        obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hχ
        have hβ1 : β 1 = 1 := one_apply_of_mem_Irr_of_commutative hβ
        show (lam * Work.Clifford.inflateFun N β) 1 = θ 1
        rw [show (lam * Work.Clifford.inflateFun N β) 1
              = lam 1 * Work.Clifford.inflateFun N β 1 from rfl,
          show Work.Clifford.inflateFun N β (1 : G) = β 1 from rfl, hβ1, mul_one, hlam1]
      rw [Finset.sum_congr rfl h3, Finset.sum_const, nsmul_eq_mul]
    rw [hid, he1, one_smul, h2] at h1
    have h4 : (((Work.CharCore.Irr (G ⧸ N)).image
        (fun β => lam * Work.Clifford.inflateFun N β)).card : ℂ) = (N.index : ℂ) :=
      mul_right_cancel₀ hθ1 h1
    exact_mod_cast h4
  · intro χ hχ
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hχ
    rw [(hdeg β hβ).2, hdegLam]
  · rw [hid, he1, one_smul]

/-- The inner product of the restriction of `ψ : ↥I → ℂ` to a subgroup `H ≤ I` against the
transport of `θ : ↥H → ℂ` to `↥(H.subgroupOf I)`, expressed through `Work.Clifford.resFunOfLe`
and complex conjugation (the two vocabularies of restriction are related by
`Subgroup.subgroupOfEquivOfLe`). -/
theorem cfInner_transport_resFun_eq_conj {X : Type*} [Group X] [Fintype X] {H I : Subgroup X}
    (hHI : H ≤ I) (θ : ↥H → ℂ) (ψ : ↥I → ℂ) :
    (Work.CharCore.cfInner (fun x : ↥(H.subgroupOf I) => θ (Subgroup.subgroupOfEquivOfLe hHI x))
        (Work.Induction.resFun (H.subgroupOf I) ψ))
      = (starRingEnd ℂ) (Work.CharCore.cfInner (Work.Clifford.resFunOfLe hHI ψ) θ) := by
  have h1 : Work.CharCore.cfInner (Work.Induction.resFun (H.subgroupOf I) ψ)
      (fun x : ↥(H.subgroupOf I) => θ (Subgroup.subgroupOfEquivOfLe hHI x))
      = Work.CharCore.cfInner (Work.Clifford.resFunOfLe hHI ψ) θ := by
    have h2 : Work.Induction.resFun (H.subgroupOf I) ψ
        = fun x => Work.Clifford.resFunOfLe hHI ψ (Subgroup.subgroupOfEquivOfLe hHI x) := by
      funext x; rfl
    rw [h2]
    exact Work.Clifford.cfInner_comp_mulEquiv (Subgroup.subgroupOfEquivOfLe hHI)
      (Work.Clifford.resFunOfLe hHI ψ) θ
  rw [Work.CharCore.cfInner_conj_symm, h1]

open Classical in
/-- **FT 4.5, Hall case, second conjunct.**  With `H ⊴ X`, `θ ∈ Irr H`, `X₀ ⊴ X` such that
`I(θ) ≤ X₀`, `X₀/H` commutative and `H` a Hall subgroup of `X₀`: if moreover `θ` extends across
the pair `H.subgroupOf I(θ) ⊴ ↥I(θ)` (the hypothesis `hext`, supplied in the application by
`Work.CharPrelim.exists_extension_of_coprime`), then `Ind_H^X θ` is the sum of `H.relIndex I(θ)`
distinct irreducible characters of `X` of degree `I(θ).index * irrDeg θ`. -/
theorem hall_conjunct_of_extension {X : Type*} [Group X] [Fintype X] {H : Subgroup X} [H.Normal]
    {θ : ↥H → ℂ} (hθ : θ ∈ Work.CharPrelim.IrrSub H) {X₀ : Subgroup X} (hX₀ : X₀.Normal)
    (hI : Work.Clifford.inertia H θ ≤ X₀) (hab : ⁅X₀, X₀⁆ ≤ H)
    (hHall : Work.CharPrelim.IsHallIn H X₀)
    (hext : ∃ lam ∈ Work.CharCore.Irr ↥(Work.Clifford.inertia H θ),
      Work.Induction.resFun (H.subgroupOf (Work.Clifford.inertia H θ)) lam
        = fun x => θ (Subgroup.subgroupOfEquivOfLe (Work.Clifford.le_inertia_of_mem_Irr
            ((Work.Clifford.mem_Irr_charCore_iff).mpr hθ)) x)) :
    ∃ T : Finset (X → ℂ), (∀ χ ∈ T, χ ∈ Work.CharCore.Irr X) ∧
      T.card = H.relIndex (Work.Clifford.inertia H θ) ∧
      (∀ χ ∈ T, Work.CharCore.irrDeg χ
        = (Work.Clifford.inertia H θ).index * Work.CharCore.irrDeg θ) ∧
      Work.Induction.indFun H θ = ∑ χ ∈ T, χ := by
  classical
  have hθ' : θ ∈ Work.Clifford.Irr ↥H := (Work.Clifford.mem_Irr_charCore_iff).mpr hθ
  have hHI : H ≤ Work.Clifford.inertia H θ := Work.Clifford.le_inertia_of_mem_Irr hθ'
  let θI : ↥(H.subgroupOf (Work.Clifford.inertia H θ)) → ℂ :=
    fun x => θ (Subgroup.subgroupOfEquivOfLe hHI x)
  haveI : Fintype (↥(Work.Clifford.inertia H θ) ⧸ H.subgroupOf (Work.Clifford.inertia H θ)) :=
    QuotientGroup.fintype _
  haveI hcommI : IsMulCommutative
      (↥(Work.Clifford.inertia H θ) ⧸ H.subgroupOf (Work.Clifford.inertia H θ)) :=
    isMulCommutative_quotient_subgroupOf hI hab
  have hθI : θI ∈ Work.CharCore.Irr ↥(H.subgroupOf (Work.Clifford.inertia H θ)) :=
    (Work.Clifford.mem_Irr_charCore_iff).mp
      (Work.Clifford.Irr_comp_mulEquiv (Subgroup.subgroupOfEquivOfLe hHI) hθ')
  have hθIinv : Work.Clifford.inertia (H.subgroupOf (Work.Clifford.inertia H θ)) θI = ⊤ := by
    simpa only [θI] using Work.Clifford.inertia_subgroupOf_eq_top hθ'
  have hidxI : (H.subgroupOf (Work.Clifford.inertia H θ)).index ∣ H.relIndex X₀ := by
    rw [show (H.subgroupOf (Work.Clifford.inertia H θ)).index
        = H.relIndex (Work.Clifford.inertia H θ) from rfl,
      ← Subgroup.relIndex_mul_relIndex H (Work.Clifford.inertia H θ) X₀ hHI hI]
    exact dvd_mul_right _ _
  have hcop : (Nat.card ↥(H.subgroupOf (Work.Clifford.inertia H θ))).Coprime
      (H.subgroupOf (Work.Clifford.inertia H θ)).index := by
    have h1 : Nat.card ↥(H.subgroupOf (Work.Clifford.inertia H θ)) = Nat.card ↥H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHI).toEquiv
    rw [h1]
    exact Nat.Coprime.coprime_dvd_right hidxI hHall.2
  have hdegθI : Work.CharCore.irrDeg θI = Work.CharCore.irrDeg θ := by
    have h3 : (Work.CharCore.irrDeg θI : ℂ) = (Work.CharCore.irrDeg θ : ℂ) := by
      rw [← Work.CharCore.irrDeg_spec hθI]
      simp only [θI, map_one]
      exact Work.CharCore.irrDeg_spec hθ
    exact_mod_cast h3
  obtain ⟨T₁, hT₁irr, hT₁card, hT₁deg, hT₁sum⟩ :=
    exists_sum_of_extension (G := ↥(Work.Clifford.inertia H θ))
      (N := H.subgroupOf (Work.Clifford.inertia H θ)) (θ := θI) hθI hθIinv hext
  -- every element of `T₁` lies over `θ`
  have hlies : ∀ χ ∈ T₁, Work.Clifford.LiesOver H (Work.Clifford.inertia H θ) hHI θ χ := by
    intro χ hχ
    have hcf : Work.CharCore.cfInner θI
        (Work.Induction.resFun (H.subgroupOf (Work.Clifford.inertia H θ)) χ) ≠ 0 := by
      rw [← Work.Induction.frobenius_reciprocity (H.subgroupOf (Work.Clifford.inertia H θ))
        θI χ (Work.CharCore.isClassFun_of_mem_Irr (hT₁irr χ hχ)), hT₁sum,
        Work.CharCore.cfInner_sum_left]
      rw [Finset.sum_congr rfl (fun χ' hχ' =>
        Work.CharCore.irr_orthonormal χ' χ (hT₁irr χ' hχ') (hT₁irr χ hχ)),
        Finset.sum_ite_eq' T₁ χ (fun _ => (1 : ℂ)), if_pos hχ]
      norm_num
    intro h0
    have h0' : Work.CharCore.cfInner (Work.Clifford.resFunOfLe hHI χ) θ = 0 := h0
    exact hcf (by rw [cfInner_transport_resFun_eq_conj hHI θ χ, h0']; exact map_zero _)
  have hInd_irr : ∀ χ ∈ T₁, Work.Induction.indFun (Work.Clifford.inertia H θ) χ
      ∈ Work.CharCore.Irr X := fun χ hχ =>
    (Work.Clifford.mem_Irr_charCore_iff).mp
      (Work.Clifford.clifford_induction_mem_Irr hθ'
        ((Work.Clifford.mem_Irr_charCore_iff).mpr (hT₁irr χ hχ)) (hlies χ hχ))
  have hsumH : Work.Induction.indFun H θ
      = ∑ χ ∈ T₁, Work.Induction.indFun (Work.Clifford.inertia H θ) χ := by
    rw [← Work.Induction.indFun_trans hHI θ]
    rw [show Work.Induction.indFun (H.subgroupOf (Work.Clifford.inertia H θ)) θI
        = ∑ χ ∈ T₁, χ from hT₁sum]
    rw [Work.Induction.indFun_sum]
  -- an induced constituent of the sum lies over `θ`
  have hInd_lies : ∀ χ ∈ T₁, Work.Clifford.IsConstituentOf θ
      (Work.Clifford.resFun H (Work.Induction.indFun (Work.Clifford.inertia H θ) χ)) := by
    intro χ hχ
    have hcf : Work.CharCore.cfInner (Work.Induction.indFun H θ)
        (Work.Induction.indFun (Work.Clifford.inertia H θ) χ) ≠ 0 := by
      rw [hsumH, Work.CharCore.cfInner_sum_left]
      rw [Finset.sum_congr rfl (fun χ' hχ' =>
        Work.CharCore.irr_orthonormal _ _ (hInd_irr χ' hχ') (hInd_irr χ hχ))]
      have hcast : (∑ χ' ∈ T₁, if Work.Induction.indFun (Work.Clifford.inertia H θ) χ'
            = Work.Induction.indFun (Work.Clifford.inertia H θ) χ then (1 : ℂ) else 0)
          = ((∑ χ' ∈ T₁, if Work.Induction.indFun (Work.Clifford.inertia H θ) χ'
              = Work.Induction.indFun (Work.Clifford.inertia H θ) χ then (1 : ℕ) else 0 : ℕ) : ℂ) := by
        rw [Nat.cast_sum]
        refine Finset.sum_congr rfl fun χ' _ => ?_
        by_cases h : Work.Induction.indFun (Work.Clifford.inertia H θ) χ'
            = Work.Induction.indFun (Work.Clifford.inertia H θ) χ <;> simp [h]
      rw [hcast]
      have hpos : 1 ≤ (∑ χ' ∈ T₁, if Work.Induction.indFun (Work.Clifford.inertia H θ) χ'
            = Work.Induction.indFun (Work.Clifford.inertia H θ) χ then (1 : ℕ) else 0) := by
        have h1 := Finset.single_le_sum (s := T₁)
          (f := fun χ' => if Work.Induction.indFun (Work.Clifford.inertia H θ) χ'
              = Work.Induction.indFun (Work.Clifford.inertia H θ) χ then (1 : ℕ) else 0)
          (fun b _ => by positivity) hχ
        simpa using h1
      exact Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hpos)
    intro h0
    have h1 : Work.CharCore.cfInner θ
        (Work.Induction.resFun H (Work.Induction.indFun (Work.Clifford.inertia H θ) χ)) = 0 := by
      have h2 : (starRingEnd ℂ) (Work.CharCore.cfInner θ
          (Work.Induction.resFun H
            (Work.Induction.indFun (Work.Clifford.inertia H θ) χ))) = 0 := by
        rw [← Work.CharCore.cfInner_conj_symm
          (Work.Induction.resFun H (Work.Induction.indFun (Work.Clifford.inertia H θ) χ))]
        exact h0
      exact (starRingEnd ℂ).injective (by rw [h2, map_zero])
    have h3 : Work.CharCore.cfInner (Work.Induction.indFun H θ)
        (Work.Induction.indFun (Work.Clifford.inertia H θ) χ) = 0 := by
      rw [Work.Induction.frobenius_reciprocity H θ _
        (Work.CharCore.isClassFun_of_mem_Irr (hInd_irr χ hχ))]
      exact h1
    exact hcf h3
  -- distinct parametrisation of the induced characters
  have hinj : Set.InjOn (fun χ => Work.Induction.indFun (Work.Clifford.inertia H θ) χ) ↑T₁ := by
    intro χ hχ χ' hχ' heq
    have hχT : χ ∈ T₁ := Finset.mem_coe.mp hχ
    have hχ'T : χ' ∈ T₁ := Finset.mem_coe.mp hχ'
    obtain ⟨ψ, -, huniq⟩ := Work.Clifford.clifford_correspondence hθ'
      ((Work.Clifford.mem_Irr_charCore_iff).mpr (hInd_irr χ hχT)) (hInd_lies χ hχT)
    have h1 : χ = ψ := huniq χ
      ⟨(Work.Clifford.mem_Irr_charCore_iff).mpr (hT₁irr χ hχT), hlies χ hχT, rfl⟩
    have h2 : χ' = ψ := huniq χ'
      ⟨(Work.Clifford.mem_Irr_charCore_iff).mpr (hT₁irr χ' hχ'T), hlies χ' hχ'T, heq.symm⟩
    rw [h1, h2]
  refine ⟨T₁.image (fun χ => Work.Induction.indFun (Work.Clifford.inertia H θ) χ), ?_, ?_, ?_, ?_⟩
  · intro χ hχ
    obtain ⟨χ', hχ', rfl⟩ := Finset.mem_image.mp hχ
    exact hInd_irr χ' hχ'
  · rw [Finset.card_image_of_injOn hinj, hT₁card]
    rfl
  · intro χ hχ
    obtain ⟨χ', hχ', rfl⟩ := Finset.mem_image.mp hχ
    have hcast : (Work.CharCore.irrDeg
        (Work.Induction.indFun (Work.Clifford.inertia H θ) χ') : ℂ)
        = (((Work.Clifford.inertia H θ).index * Work.CharCore.irrDeg θ : ℕ) : ℂ) := by
      rw [← Work.CharCore.irrDeg_spec (hInd_irr χ' hχ'), Work.Induction.indFun_apply_one,
        Work.CharCore.irrDeg_spec (hT₁irr χ' hχ'), hT₁deg χ' hχ', hdegθI]
      push_cast
      ring
    exact_mod_cast hcast
  · rw [hsumH]
    rw [Finset.sum_image (f := fun y : X → ℂ => y)
      (g := fun χ => Work.Induction.indFun (Work.Clifford.inertia H θ) χ) hinj]

end Work.CharPrelim
