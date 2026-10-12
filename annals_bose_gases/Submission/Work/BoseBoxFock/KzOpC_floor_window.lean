import ChallengeDeps
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.KafzInst
import Submission.Work.BoseBoxFock.NWindow_lift_honest
import Submission.Work.BoseBoxFock.bddBelow_valFS_range_rho
import Submission.Work.BoseBoxFock.bomb_KzOpFS_level0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.KzOpC_floor_window`

**The `KzOpC` floor for real window vectors.**  This is the step (F2) of
`KAFZ_STATUS4.md` §6 / `KAFZ_STATUS5.md` §4: for a vector `x` of the spectator space
whose canonical coordinates are real (`hre`) and which lies in FS's window
`1_{[0,𝓜]}(n₊)` with `𝓜 = 𝓜_hon` (`hdec`), the *globally* minimised Rayleigh quotient
`λ := ⨅_{ρ' ≥ 0} valFS ρ'` of the honest family is a lower bound for the quadratic form
of the spectator operator `KzOpC … ρ` at the *given* `ρ`:

    `λ ‖x‖² ≤ Re ⟪x, KzOpC (HM μ).f (HM μ).g BNHHon F E (8πa v) ρ x⟫`.

(`KzOpC` is FS `eq:Kz` on the zero-condensate slice, `KzOpC.lean`; the transport of the
relevant symbols is `bomb_KzOpFS_level0`.)

## Route

* `exists_excLift` lifts `x` to the condensate-free mode-lattice state
  `f = liftL g` with `split f = single 0 x`, `g` the (real) coordinate family of `x`;
* `NWindow_of_support_degree` converts a bound `deg α ≤ 𝓜` for `α ∈ supp f` into the
  window hypothesis `T.NWindow 𝓜 f`.  The degree bound is supplied by
  `support_liftL_degree_le` (the lift only sits on the `lift β`, `deg (lift β) = deg β`)
  and `coord_eq_zero_of_floor_lt` (the `nPlusC`-eigenvalue decomposition of `hdec`,
  transported to the `Finsupp` model by `nPlusC_toCFock`, kills every coefficient of
  `x` of degree `> ⌊𝓜⌋₊`);
* `valFS_le_rayleigh` (with the fixed-`ρ` boundedness `bddBelow_valFS_honest`) gives
  `valFS ρ ≤ qw f (KzOpFS ρ)/normSq f`, `bddBelow_valFS_range_rho` gives
  `⨅_{ρ'} valFS ρ' ≤ valFS ρ` (`ciInf_le`), and `bomb_KzOpFS_level0` transports the
  Rayleigh quotient to `Re ⟪x, KzOpC … ρ x⟫`; `normSq f = ‖x‖²` by `Split_inner`.

## Note on the scope of `π`

The statement writes the coupling `ĝ(0) = 8π a v` as `8 * π * BoseGases.a v`, i.e. with the
notation `π` of `Real.pi` — exactly as `HonestBoxFam`'s `gHat0 = 8 * π * a v`
(`Defs.lean`, where `open scoped Real` is in force).  We therefore `open scoped Real` here
too; without it, `π` would be *auto-bound* as an implicit variable (this file does not set
`autoImplicit false`), the statement would quantify over an arbitrary real `π`, and it would
be false (the `c`-number row of `KzOpC` is affine in `ĝ(0)` with negative slope
`½ℓ³ρ(ρ−2μ)` in the regime `0 < ρ < 2μ`).
-/

open scoped BigOperators Real

open Work.BoseB4

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. The number operator on the monomial basis -/

/-- `modeNumOp m i` multiplies the monomial `x^α` by the occupation number `α i`. -/
lemma deg_modeNumOp_single {m : ℕ} (i : Fin m) (α : Fin m →₀ ℕ) (c : ℝ) :
    Work.BoseB4.modeNumOp m i (Finsupp.single α c) = (α i : ℝ) • Finsupp.single α c := by
  rw [Work.BoseB4.modeNumOp, LinearMap.comp_apply, Work.BoseB4.ann_single_basis, map_smul,
    Work.BoseB4.cre_single]
  by_cases h : α i = 0
  · rw [h]; simp
  · have hsub : α - Work.BoseB4.e m i + Work.BoseB4.e m i = α := by
      ext j
      rw [Finsupp.add_apply]
      by_cases hj : j = i
      · subst hj
        rw [Finsupp.tsub_apply, Work.BoseB4.e, Finsupp.single_eq_same]; omega
      · rw [Finsupp.tsub_apply, Work.BoseB4.e, Finsupp.single_eq_of_ne hj, add_zero, tsub_zero]
    rw [hsub]
    rw [Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one]

/-- `totNumOp m` multiplies the monomial `x^α` by its total degree. -/
lemma deg_totNumOp_single {m : ℕ} (α : Fin m →₀ ℕ) (c : ℝ) :
    Work.BoseB4.totNumOp m (Finsupp.single α c)
      = (((Finsupp.degree α : ℕ) : ℝ)) • Finsupp.single α c := by
  rw [Work.BoseB4.totNumOp, LinearMap.sum_apply]
  rw [Finset.sum_congr rfl (fun i _ => deg_modeNumOp_single i α c)]
  rw [← Finset.sum_smul, Finsupp.degree_eq_sum, Nat.cast_sum]

/-- The degree-`j` part of a mode state is a `totNumOp`-eigenvector of eigenvalue `j`. -/
lemma deg_totNumOp_filter {m : ℕ} (f : Work.BoseB4.RealFock m) (j : ℕ) :
    Work.BoseB4.totNumOp m (f.filter (fun α => Finsupp.degree α = j))
      = (j : ℝ) • (f.filter (fun α => Finsupp.degree α = j)) := by
  induction f using Finsupp.induction_linear with
  | zero => rw [Finsupp.filter_zero, map_zero, smul_zero]
  | add f g hf hg => rw [Finsupp.filter_add, map_add, hf, hg, smul_add]
  | single α c =>
      by_cases h : Finsupp.degree α = j
      · rw [Finsupp.filter_single_of_pos (fun α => Finsupp.degree α = j) h, deg_totNumOp_single, h]
      · rw [Finsupp.filter_single_of_neg (fun α => Finsupp.degree α = j) h, map_zero, smul_zero]

/-- **The window condition from a support-degree bound**: a mode state whose monomials all
have total degree `≤ M` lies in FS's window `1_{[0,M]}(n₊)`. -/
theorem NWindow_of_support_degree (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    (μ M : ℝ) (f : Work.BoseB4.RealFock (HM μ).m)
    (hd : ∀ α : Fin (HM μ).m →₀ ℕ, f α ≠ 0 → ((Finsupp.degree α : ℕ) : ℝ) ≤ M) :
    (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NWindow M f := by
  refine ⟨fun m => f.filter (fun α => Finsupp.degree α = m), ?_, ?_⟩
  · intro m
    show Work.BoseB4.totNumOp (HM μ).m (f.filter (fun α => Finsupp.degree α = m))
      = (m : ℝ) • (f.filter (fun α => Finsupp.degree α = m))
    exact deg_totNumOp_filter f m
  · show f = ∑ m ∈ Finset.range (⌊M⌋₊ + 1), f.filter (fun α => Finsupp.degree α = m)
    ext α
    rw [Finsupp.finsetSum_apply]
    simp only [Finsupp.filter_apply]
    rw [Finset.sum_ite_eq]
    by_cases hmem : Finsupp.degree α ∈ Finset.range (⌊M⌋₊ + 1)
    · rw [if_pos hmem]
    · rw [if_neg hmem]
      by_contra hf
      have hge : ⌊M⌋₊ + 1 ≤ Finsupp.degree α := by
        rw [Finset.mem_range] at hmem; omega
      have h1 : ((Finsupp.degree α : ℕ) : ℝ) ≤ M := hd α hf
      have h2 : M < (⌊M⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one M
      have h3 : ((⌊M⌋₊ + 1 : ℕ) : ℝ) ≤ ((Finsupp.degree α : ℕ) : ℝ) := by
        exact_mod_cast hge
      push_cast at h3
      linarith

/-! ## 1. The degree operator on the `Finsupp` model of the spectator space -/

/-- The `β`-coefficient of the `n₊`-degree multiplication on the `Finsupp` model. -/
lemma sum_degree_single_apply {X : Type*} [DecidableEq X]
    (w : (X →₀ ℕ) →₀ ℂ) (β : X →₀ ℕ) :
    (w.sum (fun β' c => ((((Finsupp.degree β' : ℕ) : ℝ)) : ℂ) • Finsupp.single β' c)) β
      = (((((Finsupp.degree β : ℕ) : ℝ)) : ℂ)) * w β := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.sum_add_index', Finsupp.add_apply, hf, hg, Finsupp.add_apply]
    · ring
    · intro β'; simp
    · intro β' b1 b2; rw [Finsupp.single_add, smul_add]
  | single β' c =>
    rw [Finsupp.sum_single_index (by simp), Finsupp.smul_apply, smul_eq_mul]
    by_cases hh : β' = β
    · rw [hh, Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne (Ne.symm hh), mul_zero, mul_zero]

/-- **The `n₊`-window kills the coefficients above the floor.**  If `x` is a finite sum of
`nPlusC`-eigenvectors with eigenvalues `j ≤ ⌊M⌋₊` (FS's window, algebraically), then every
coefficient of `x` of total degree `> ⌊M⌋₊` vanishes.  Here `nPlusC` acts on the `Finsupp`
model as multiplication by the total degree (`nPlusC_toCFock`), so each eigenvector is
supported on its own degree. -/
theorem coord_eq_zero_of_floor_lt {m : ℕ} [NeZero m] {M : ℝ}
    (x : Work.BoseB4.cfock (Work.BoseB4.Excited m))
    (hdec : ∃ φ : ℕ → Work.BoseB4.cfock (Work.BoseB4.Excited m),
      (∀ j : ℕ, Work.BoseBoxFock.nPlusC (m := m) (φ j) = (j : ℝ) • φ j)
        ∧ x = ∑ j ∈ Finset.range (⌊M⌋₊ + 1), φ j)
    (β : Work.BoseB4.Excited m →₀ ℕ) (hβ : ⌊M⌋₊ < Finsupp.degree β) :
    ((Work.BoseB4.toCFock (Work.BoseB4.Excited m)).symm x) β = 0 := by
  obtain ⟨φ, hφ, hx⟩ := hdec
  have key : ∀ j : ℕ, ((((((Finsupp.degree β : ℕ) : ℝ)) : ℂ)) - (j : ℂ))
      * ((toCFock (Excited m)).symm (φ j)) β = 0 := by
    intro j
    have hsumj : ((toCFock (Excited m)).symm (φ j)).sum
          (fun β' c => ((((Finsupp.degree β' : ℕ) : ℝ)) : ℂ) • Finsupp.single β' c)
        = (j : ℂ) • ((toCFock (Excited m)).symm (φ j)) := by
      apply (toCFock (Excited m)).injective
      rw [← nPlusC_toCFock, LinearEquiv.apply_symm_apply, hφ j, map_smul,
        LinearEquiv.apply_symm_apply]
      exact Complex.coe_smul j (φ j)
    have hcoeff : ((((((Finsupp.degree β : ℕ) : ℝ)) : ℂ))
          * ((toCFock (Excited m)).symm (φ j)) β)
        = (j : ℂ) * ((toCFock (Excited m)).symm (φ j)) β := by
      have h := congrArg (fun (z : (Excited m →₀ ℕ) →₀ ℂ) => z β) hsumj
      rw [sum_degree_single_apply, Finsupp.smul_apply, smul_eq_mul] at h
      exact h
    rw [sub_mul, hcoeff, sub_self]
  have hzero : ∀ j ∈ Finset.range (⌊M⌋₊ + 1),
      ((toCFock (Excited m)).symm (φ j)) β = 0 := by
    intro j hj
    have hjle : j ≤ ⌊M⌋₊ := by
      rw [Finset.mem_range] at hj; omega
    have hc : ((((((Finsupp.degree β : ℕ) : ℝ)) : ℂ)) - (j : ℂ)) ≠ 0 := by
      rw [sub_ne_zero]
      have hne : (Finsupp.degree β : ℕ) ≠ j := by omega
      exact_mod_cast hne
    exact (mul_eq_zero.mp (key j)).resolve_left hc
  have hsymm : ((toCFock (Excited m)).symm x)
      = ∑ j ∈ Finset.range (⌊M⌋₊ + 1), (toCFock (Excited m)).symm (φ j) := by
    rw [hx, map_sum]
  rw [hsymm, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero hzero

/-- **The support-degree bound of the condensate-free lift** `liftL g`: every nonzero
coefficient of `liftL g` sits at some `lift β` with `g β ≠ 0`, and
`deg (lift β) = deg β` (`embDomain` preserves the total degree). -/
theorem support_liftL_degree_le {m : ℕ} [NeZero m] (M : ℝ)
    (g : (Excited m →₀ ℕ) →₀ ℝ)
    (hg : ∀ β : Excited m →₀ ℕ, g β ≠ 0 → ((Finsupp.degree β : ℕ) : ℝ) ≤ M) :
    ∀ α : Fin m →₀ ℕ, (ExcLift.liftL g) α ≠ 0 → ((Finsupp.degree α : ℕ) : ℝ) ≤ M := by
  have hdeg : ∀ β : Excited m →₀ ℕ,
      ((Finsupp.degree (ExcLift.lift β) : ℕ) : ℝ) = ((Finsupp.degree β : ℕ) : ℝ) := by
    intro β
    rw [ExcLift.lift, Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain]
  have hformula : ∀ g : (Excited m →₀ ℕ) →₀ ℝ, ∀ α : Fin m →₀ ℕ,
      (ExcLift.liftL g) α = g.sum (fun β c => c * (1 / fockW 0 β)
            * (Finsupp.single (ExcLift.lift β) (1:ℝ)) α) := by
    intro g
    induction g using Finsupp.induction_linear with
    | zero => intro α; simp
    | add f g hf hg =>
      intro α
      rw [map_add, Finsupp.add_apply, hf α, hg α]
      rw [Finsupp.sum_add_index']
      · intro β; simp
      · intro β b1 b2; ring
    | single β a =>
      intro α
      rw [ExcLift.liftL_single, Finsupp.sum_single_index (by simp)]
      rw [Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
      ring
  intro α hne
  rw [hformula g α] at hne
  rw [Finsupp.sum_of_support_subset g (Finset.Subset.refl _) _ (fun i hi => by simp)] at hne
  obtain ⟨β, hβmem, hβne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hβ0 : g β ≠ 0 := by
    intro h0; rw [h0, zero_mul, zero_mul] at hβne; exact hβne rfl
  have hαβ : α = ExcLift.lift β := by
    by_contra h
    rw [Finsupp.single_eq_of_ne h, mul_zero] at hβne
    exact hβne rfl
  rw [hαβ, hdeg β]
  exact hg β hβ0

/-! ## 2. The floor -/

theorem KzOpC_floor_window (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    (μ C Kw Kχ ρ : ℝ) (hμ : 0 < μ) (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hKw : 0 ≤ Kw) (hKχ : 0 ≤ Kχ)
    (henv : EnvFactsAt v h fc fu HM μ C)
    (hWω : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
      |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega k| ≤ Kw)
    (hχb : (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChiSq s ^ 2) ≤ Kχ)
    (x : Work.BoseB4.cfock (Work.BoseB4.Excited (HM μ).m))
    (hre : ∀ β : Work.BoseB4.Excited (HM μ).m →₀ ℕ,
      ((Work.BoseB4.toCFock (Work.BoseB4.Excited (HM μ).m)).symm x β).im = 0)
    (hdec : ∃ φ : ℕ → Work.BoseB4.cfock (Work.BoseB4.Excited (HM μ).m),
      (∀ j : ℕ, Work.BoseBoxFock.nPlusC (m := (HM μ).m) (φ j) = (j : ℝ) • φ j)
        ∧ x = ∑ j ∈ Finset.range (⌊(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM⌋₊ + 1), φ j) :
    (⨅ (ρ' : {ρ : ℝ // 0 ≤ ρ}),
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).valFS ρ'.1) * ‖x‖ ^ 2
      ≤ (inner ℂ x (Work.BoseBoxFock.KzOpC (HM μ).f (HM μ).g
            (Work.BoseBoxFock.BNHHon v h fc fu HM μ)
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
            (8 * π * BoseGases.a v) ρ x)).re := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, hω0, -, -, -, -, -, -, -⟩ := henv
  -- `𝓜 = (HonestBoxFam …).E.bigM ≥ 0`
  have hM0 : 0 ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM := by
    show 0 ≤ Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
    exact (Work.BoseBox.bigM_pos_of_params hμ hav).le
  -- ## the condensate-free lift of `x`
  set vc : (Work.BoseB4.Excited (HM μ).m →₀ ℕ) →₀ ℂ :=
    (Work.BoseB4.toCFock (Work.BoseB4.Excited (HM μ).m)).symm x with hvc
  set g : (Work.BoseB4.Excited (HM μ).m →₀ ℕ) →₀ ℝ := vc.mapRange Complex.re (by simp) with hgmr
  set f : Work.BoseB4.RealFock (HM μ).m := Work.BoseBoxFock.ExcLift.liftL g with hflift
  have hsplit : Work.BoseB4.split f = Finsupp.single 0 x := by
    have hV : Finsupp.mapRange (fun r : ℝ => (r : ℂ)) (by simp) g = vc := by
      ext β
      rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply]
      exact Work.BoseBoxFock.ExcLift.ofReal_re_of_im_zero (hre β)
    rw [hflift, Work.BoseBoxFock.ExcLift.split_liftL, Work.BoseBoxFock.ExcLift.levelL_eq, hV]
    exact congrArg (Finsupp.single (0 : ℕ))
      (LinearEquiv.apply_symm_apply (Work.BoseB4.toCFock (Work.BoseB4.Excited (HM μ).m)) x)
  -- ## the degree bound on `supp f`
  have hdeg : ∀ α : Fin (HM μ).m →₀ ℕ, f α ≠ 0 →
      ((Finsupp.degree α : ℕ) : ℝ) ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM := by
    have hgβ : ∀ β : Work.BoseB4.Excited (HM μ).m →₀ ℕ, g β ≠ 0 →
        ((Finsupp.degree β : ℕ) : ℝ) ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM := by
      intro β hβ
      by_contra hcon
      have hcon' : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM
          < ((Finsupp.degree β : ℕ) : ℝ) := not_le.mp hcon
      have hfl : ⌊(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM⌋₊ < Finsupp.degree β := by
        have h1 : ((⌊(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM⌋₊ : ℕ) : ℝ)
            ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM := Nat.floor_le hM0
        have h2 : ((⌊(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM⌋₊ : ℕ) : ℝ)
            < ((Finsupp.degree β : ℕ) : ℝ) := lt_of_le_of_lt h1 hcon'
        exact_mod_cast h2
      have hv0 : vc β = 0 := coord_eq_zero_of_floor_lt x hdec β hfl
      have hg0 : g β = 0 := by
        rw [hgmr, Finsupp.mapRange_apply, hv0]; simp
      exact hβ hg0
    simpa only [hflift] using
      support_liftL_degree_le (M := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM)
        g hgβ
  have hwin : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NWindow
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM f :=
    NWindow_of_support_degree v h fc fu HM μ _ f hdeg
  by_cases hx0 : x = 0
  · rw [hx0]; simp
  · -- ## the Rayleigh quotient of the lift
    have hfne : f ≠ 0 := by
      intro hf0
      have h1 : Finsupp.single (0 : ℕ) x = 0 := by rw [← hsplit, hf0, map_zero]
      exact hx0 (Finsupp.single_eq_zero.mp h1)
    have hnormSq : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f = ‖x‖ ^ 2 := by
      show (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.bp f f = ‖x‖ ^ 2
      have h3 : Work.BoseB4.bomb (HM μ).m f f = ‖x‖ ^ 2 := by
        have hsin := Work.BoseB4.Split_inner f f
        rw [hsplit, Work.BoseBoxFock.coreInner_single_zero] at hsin
        have hre2 := congrArg Complex.re hsin
        rw [Work.BoseB4.re_inner_self, Complex.ofReal_re] at hre2
        exact hre2.symm
      exact h3
    have hray := Work.BoseBoxFock.valFS_le_rayleigh
      (Mode := Work.BoseBoxFock.Lab (HM μ).N)
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ) ρ f
      (Work.BoseBoxFock.bddBelow_valFS_honest v h fc fu HM μ ρ hρ) hwin hfne
    have hIle : (⨅ (ρ' : {ρ : ℝ // 0 ≤ ρ}),
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).valFS ρ'.1)
        ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).valFS ρ :=
      ciInf_le (Work.BoseBoxFock.bddBelow_valFS_range_rho v h fc fu HM μ Kw Kχ hμ hav
        hω0 hWω hKχ hχb) ⟨ρ, hρ⟩
    have h1 : (⨅ (ρ' : {ρ : ℝ // 0 ≤ ρ}),
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).valFS ρ'.1) * ‖x‖ ^ 2
        ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).valFS ρ * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hIle (sq_nonneg _)
    have h2 : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).valFS ρ * ‖x‖ ^ 2
        ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
            (Work.BoseBoxFock.KzOpFS (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0 ρ) := by
      have hpos : 0 < (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f :=
        Work.BoseFixR.normSq_pos _ hfne
      have hne : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f ≠ 0 :=
        ne_of_gt hpos
      have hmul := mul_le_mul_of_nonneg_right hray hpos.le
      rw [div_mul_cancel₀ _ hne] at hmul
      rwa [hnormSq] at hmul
    have htr : Work.BoseB4.bomb (HM μ).m f
        ((Work.BoseBoxFock.KzOpFS (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0 ρ) f)
        = (inner ℂ x (Work.BoseBoxFock.KzOpC (HM μ).f (HM μ).g
            (Work.BoseBoxFock.BNHHon v h fc fu HM μ)
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
            (8 * π * BoseGases.a v) ρ x)).re := by
      exact Work.BoseBoxFock.bomb_KzOpFS_level0 (B := Work.BoseK15.corpusBox)
        (kmom := Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N)
        (hkmom := Work.BoseBoxFock.kmomLab_neg (Work.BoseBoxFock.ellH v μ) (HM μ).N)
        (f := (HM μ).f) (g := (HM μ).g) (hf := (HM μ).hf)
        (T := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T)
        (E := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
        (gHat0 := 8 * π * BoseGases.a v) (ρ := ρ) hρ (HM μ).hf0
        (Work.BoseBoxFock.BNHHon v h fc fu HM μ)
        (Work.BoseBoxFock.hN_honest v h fc fu HM μ)
        (Work.BoseBoxFock.hNH_BNHHon v h fc fu HM μ)
        (Work.BoseBoxFock.hTa_honest v h fc fu HM μ)
        (Work.BoseBoxFock.hTaDag_honest v h fc fu HM μ) f x hsplit
    have h3 : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
          (Work.BoseBoxFock.KzOpFS (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0 ρ)
        = (inner ℂ x (Work.BoseBoxFock.KzOpC (HM μ).f (HM μ).g
            (Work.BoseBoxFock.BNHHon v h fc fu HM μ)
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
            (8 * π * BoseGases.a v) ρ x)).re := by
      have hbq : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
            (Work.BoseBoxFock.KzOpFS (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0 ρ)
          = Work.BoseB4.bomb (HM μ).m f
              ((Work.BoseBoxFock.KzOpFS (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
                (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T
                (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0 ρ) f) := by
        show Work.BoseB4.bomb (HM μ).m
            ((Work.BoseBoxFock.KzOpFS (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0 ρ) f) f
          = Work.BoseB4.bomb (HM μ).m f
              ((Work.BoseBoxFock.KzOpFS (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
                (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T
                (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0 ρ) f)
        exact Work.BoseB4.Bomb_symm _ _
      rw [hbq]
      exact htr
    exact le_trans h1 (le_trans h2 (le_of_eq h3))

end Work.BoseBoxFock
