/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/Assembly.lean` — **E6**: `global_strong2`

This is the last item of the design (`FTS_HARD_DESIGN.md` (B), **E6**): from the per-interval
limits of the `ε`-scheme (`E5`, `Submission/Work/FTS/StrongEps/EpsLimit.lean`) assemble the
*global* strong solution of the dynamic modulated equation with the regularity package
`RegPkgMin` and the a-priori bound — the conclusion `global_strong2` of the lead's statement file.

The assembly is the `pIdx`-style gluing of `Work.FTS.StrongGlobal`:

* the interval `[0, Tn n]` with `Tn n = n+1` carries a limit `g n` (`EpsLimPkg`), and two limits
  agree on the overlap — this is the *uniqueness* clause of `E5`
  (`EpsUniforpm.exists_lim`), i.e. the difference estimate of the design;
* the glued family is `G z θ τ = g (pidx τ) z θ τ` for `τ ≥ 0`, `pidx τ = ⌊τ⌋₊ + 1` (and `g 0`
  for `τ < 0`);
* every clause of `RegPkgMin`/`IsDynGSolWith` is read at `τ` from the piece `pidx τ`, using that
  `G` agrees with that piece on the whole interval `[0, Tn (pidx τ)]` — which is a *neighbourhood*
  of `τ` within `[0,∞)`.

Nothing is restarted from a limit slice: the `ℋ⁶`-bound is carried by the pieces (it is in
`EpsLimPkg`) and the glued family needs no new energy estimate.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.EpsLimit
import Submission.Work.FTS.StrongEps.EpsLimitDefsG
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongGlobal.dynRHS_congr

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS gdot IsDynEqOn IsDynGSolWith)

set_option autoImplicit false

/-! ## The interval covering -/

/-- The length of the `n`-th interval: `Tn n = n + 1`. -/
def Tn (n : ℕ) : ℝ := (n : ℝ) + 1

theorem Tn_pos (n : ℕ) : 0 < Tn n := by
  simp only [Tn]; exact lt_of_lt_of_le zero_lt_one (by norm_num)

/-- The index of the piece covering `τ`: `⌊τ⌋₊ + 1`, so that `τ < Tn (pidx τ)`. -/
def pidx (τ : ℝ) : ℕ := Nat.floor τ + 1

theorem pidx_pos (τ : ℝ) : 0 < pidx τ := Nat.succ_pos _

theorem pidx_cast (τ : ℝ) : ((pidx τ : ℕ) : ℝ) = ((Nat.floor τ : ℕ) : ℝ) + 1 := by
  simp only [pidx, Nat.cast_add, Nat.cast_one]

theorem lt_Tn_pidx (τ : ℝ) : τ < Tn (pidx τ) := by
  have h := Nat.lt_floor_add_one τ
  simp only [Tn, pidx_cast]
  linarith

theorem le_Tn_pidx (τ : ℝ) : τ ≤ Tn (pidx τ) := le_of_lt (lt_Tn_pidx τ)

/-- `Icc 0 b` is a neighbourhood of `x` within `Ici 0` as soon as `x < b`. -/
theorem Icc_zero_mem_nhdsWithin_Ici {b x : ℝ} (hxb : x < b) :
    Set.Icc (0 : ℝ) b ∈ 𝓝[Set.Ici (0 : ℝ)] x := by
  have h1 : Set.Ici (0 : ℝ) ∩ Set.Iio b ∈ 𝓝[Set.Ici (0 : ℝ)] x :=
    Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hxb))
  refine Filter.mem_of_superset h1 ?_
  rintro y ⟨hy0, hyb⟩
  exact ⟨hy0, le_of_lt hyb⟩

/-! ## The glued family and its agreement with the pieces -/

/-- The glued family: at `τ ≥ 0` it is the piece `pidx τ`, and at `τ < 0` the first piece. -/
def glued (g : ℕ → Fam) : Fam := fun z θ τ =>
  if 0 ≤ τ then g (pidx τ) z θ τ else g 0 z θ τ

@[simp] theorem glued_of_nonneg {g : ℕ → Fam} {τ : ℝ} (hτ : 0 ≤ τ) (z θ : ℝ) :
    glued g z θ τ = g (pidx τ) z θ τ := if_pos hτ

/-- **The uniqueness clause of `E5`**: two pieces agree whenever both are controlled at `τ`. -/
theorem piece_eq_at {α C₀ K : ℝ} {Cd : ℕ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g : ℕ → Fam}
    (hlim : ExistsLimH α C₀ K Φs E g₀)
    (hpk : ∀ n, EpsLimPkg α C₀ K (Cd n) (Tn n) Φs E g₀ (g n))
    {τ : ℝ} (hτ : 0 ≤ τ) {m n : ℕ} (hm : τ ≤ Tn m) (hn : τ ≤ Tn n) (z θ : ℝ) :
    g m z θ τ = g n z θ τ := by
  rcases eq_or_lt_of_le hτ with h0 | hpos
  · rw [← h0, (hpk m).init z θ, (hpk n).init z θ]
  · obtain ⟨_, _, h, _, hu⟩ := hlim τ hpos
    have hm' : EpsLimPkg α C₀ K (Cd m) τ Φs E g₀ (g m) := (hpk m).mono hm hτ
    have hn' : EpsLimPkg α C₀ K (Cd n) τ Φs E g₀ (g n) := (hpk n).mono hn hτ
    rw [hu (Cd m) (g m) hm' z θ τ hτ le_rfl, hu (Cd n) (g n) hn' z θ τ hτ le_rfl]

/-- The glued family agrees with the covering piece on the whole interval `[0, Tn (pidx τ)]`. -/
theorem glued_eq_piece {α C₀ K : ℝ} {Cd : ℕ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g : ℕ → Fam}
    (hlim : ExistsLimH α C₀ K Φs E g₀)
    (hpk : ∀ n, EpsLimPkg α C₀ K (Cd n) (Tn n) Φs E g₀ (g n))
    {τ : ℝ} (hτ : 0 ≤ τ) (z θ : ℝ) :
    ∀ τ' ∈ Set.Icc 0 (Tn (pidx τ)), glued g z θ τ' = g (pidx τ) z θ τ' := by
  intro τ' hτ'
  rw [glued_of_nonneg hτ'.1 z θ]
  exact (piece_eq_at hlim hpk hτ'.1 hτ'.2 (le_Tn_pidx τ') z θ).symm

/-! ## Two congruence facts for the glued family -/

theorem glued_slice {g : ℕ → Fam} {τ : ℝ} (hτ : 0 ≤ τ) :
    slice (glued g) τ = slice (g (pidx τ)) τ := by
  funext z θ
  exact glued_of_nonneg hτ z θ

/-- The glued family agrees with the covering piece on the *open* interval
`(0, Tn (pidx τ))`; this is the form in which the agreement is used for the fake-time derivative. -/
theorem glued_eq_piece_Ioo {α C₀ K : ℝ} {Cd : ℕ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g : ℕ → Fam}
    (hlim : ExistsLimH α C₀ K Φs E g₀)
    (hpk : ∀ n, EpsLimPkg α C₀ K (Cd n) (Tn n) Φs E g₀ (g n))
    {τ : ℝ} (hτ : 0 ≤ τ) (z θ : ℝ) :
    ∀ τ' ∈ Set.Ioo 0 (Tn (pidx τ)), glued g z θ τ' = g (pidx τ) z θ τ' := by
  intro τ' hτ'
  rw [glued_of_nonneg hτ'.1.le z θ]
  exact piece_eq_at hlim hpk hτ'.1.le (le_Tn_pidx τ') (le_of_lt hτ'.2) z θ

/-! ## E6 — `global_strong2` -/

/-- **E6, with the limit isolated**: the assembly takes as input exactly the conclusion of `E5`
(`EpsUniform.exists_lim`), so that it can be used with any proof of the limit step.

The proof is the gluing described in the module header: the limits of `E5` on the intervals
`[0, n+1]` are consistent by the uniqueness clause of `E5`, and the patched family
`glued g z θ τ = g (pidx τ) z θ τ` inherits every clause from the piece that covers `τ`. -/
theorem global_strong2_of_lim {α C₀ K : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g₀ : Fn}
    (hlim : ExistsLimH α C₀ K Φs E g₀) :
    ∃ g : Fam, IsDynGSolWith (Work.FTS.StrongGlobal.IsBslSolPos α) α
        (Work.FTS.Nonlin.PsiCan Φs E g) g ∧ (∀ z θ, g z θ 0 = g₀ z θ) ∧
      Work.FTS.StrongGlobal.RegPkgMin α g ∧
      (∀ τ, 0 ≤ τ → Work.FTS.Nonlin.Xn α (slice g τ) ≤ C₀ * α ^ 2) ∧
      LimApproxSE α C₀ Φs E g := by
  choose Cd _hCdpos g hpk _huniq using fun n : ℕ => hlim (Tn n) (Tn_pos n)
  have hlim' : ExistsLimH α C₀ K Φs E g₀ := hlim
  have hG : ∀ {τ : ℝ}, 0 ≤ τ → ∀ z θ, ∀ τ' ∈ Set.Icc 0 (Tn (pidx τ)),
      glued g z θ τ' = g (pidx τ) z θ τ' := fun hτ z θ => glued_eq_piece hlim' hpk hτ z θ
  have hGI : ∀ {τ : ℝ}, 0 ≤ τ → ∀ z θ, ∀ τ' ∈ Set.Ioo 0 (Tn (pidx τ)),
      glued g z θ τ' = g (pidx τ) z θ τ' := fun hτ z θ => glued_eq_piece_Ioo hlim' hpk hτ z θ
  -- **G2 / `LimApprox`**: the approximation clause of the strong output.  It is glued with the
  -- *uniqueness* clause of `ExistsLimH` and with **one** piece covering the whole of `[0,T]`
  -- (`N` with `T ≤ Tn N`): on `[0,T]` the glued family agrees with the piece `g N`, so the
  -- witnessing families `gn` of `g N` also witness the clause for `glued g`.  (The per-`τ` gluing
  -- used for `dbd` is *not* enough here: the witnessing sequence must be common to all `τ`.)
  have hApprox : LimApproxSE α C₀ Φs E (glued g) := by
    intro T hT
    obtain ⟨N, hN⟩ : ∃ N : ℕ, T ≤ Tn N :=
      ⟨Nat.ceil T, by
        have h := Nat.le_ceil T
        simp only [Tn]
        push_cast
        linarith⟩
    obtain ⟨gn, B, L, hb, hlip, hjet, hmu⟩ := (hpk N).limApprox T hT hN
    have hs : ∀ {τ : ℝ}, τ ∈ Set.Icc (0 : ℝ) T → ∀ z' θ', glued g z' θ' τ = g N z' θ' τ := by
      intro τ hτ z' θ'
      rw [glued_of_nonneg hτ.1 z' θ']
      exact piece_eq_at hlim' hpk hτ.1 (le_Tn_pidx τ) (le_trans hτ.2 hN) z' θ'
    have hsSlice : ∀ {τ : ℝ}, τ ∈ Set.Icc (0 : ℝ) T → slice (glued g) τ = slice (g N) τ := by
      intro τ hτ
      funext z' θ'
      simp only [slice]
      exact hs hτ z' θ'
    refine ⟨gn, B, L, hb, hlip, ?_, ?_⟩
    · intro τ hτ j i hji z θ hzθ
      rw [hsSlice hτ]
      exact hjet τ hτ j i hji z θ hzθ
    · intro τ hτ
      have hPsi : slice (Work.FTS.Nonlin.PsiCan Φs E (glued g)) τ
          = slice (Work.FTS.Nonlin.PsiCan Φs E (g N)) τ := by
        funext z' θ'
        simp only [Work.FTS.Nonlin.PsiCan, slice]
        rw [hsSlice hτ]
      have hF : Work.Construction.Ftau α (glued g) τ = Work.Construction.Ftau α (g N) τ := by
        funext z' θ'
        simp only [Work.Construction.Ftau]
        rw [hs hτ z' θ']
      have hmuEq : Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (glued g))
            (glued g) τ
          = Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (g N)) (g N) τ := by
        simp only [Work.FTS.Galerkin.muDyn]
        rw [hF, hsSlice hτ, hPsi]
      rw [hmuEq]
      exact hmu τ hτ
  refine ⟨glued g, ?_, ?_, ?_, ?_, hApprox⟩
  · -- the dynamic modulated equation with the positivised law
    refine ⟨?_, ?_⟩
    · intro τ hτ
      have hs : slice (g (pidx τ)) τ = slice (glued g) τ := (glued_slice hτ).symm
      exact ((hpk (pidx τ)).law τ hτ (le_Tn_pidx τ)).congr
        (Work.FTS.StrongGlobal.Ftau_congr hs) (Work.FTS.StrongGlobal.slice_PsiCan_congr hs)
    · intro z θ τ hτ hz
      have hmem : Set.Icc (0 : ℝ) (Tn (pidx τ)) ∈ 𝓝[Set.Ici (0 : ℝ)] τ :=
        Icc_zero_mem_nhdsWithin_Ici (lt_Tn_pidx τ)
      have hfun : (fun s => glued g z θ s) =ᶠ[𝓝[Set.Ici (0 : ℝ)] τ]
          (fun s => g (pidx τ) z θ s) := by
        filter_upwards [hmem] with τ' hτ'
        exact hG hτ z θ τ' hτ'
      have hval : glued g z θ τ = g (pidx τ) z θ τ := hG hτ z θ τ ⟨hτ, le_Tn_pidx τ⟩
      have hgoal := (((hpk (pidx τ)).eqT τ hτ (le_Tn_pidx τ) z θ hz).mono_of_mem_nhdsWithin
        hmem).congr_of_eventuallyEq hfun hval
      show HasDerivWithinAt (fun s => glued g z θ s) (rhsFun α Φs E (glued g) τ z θ)
        (Set.Ici (0 : ℝ)) τ
      rw [rhsFun_congr (glued_slice hτ)]
      exact hgoal
  · -- the datum
    intro z θ
    rw [glued_of_nonneg le_rfl]
    exact (hpk (pidx 0)).init z θ
  · -- the regularity package
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- joint C¹
      intro p hp
      have hτpos : 0 < p.2.2 := hp.2.2
      have hp' : p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioo 0 (Tn (pidx p.2.2)) :=
        ⟨hp.1, hp.2.1, hτpos, lt_Tn_pidx p.2.2⟩
      have hnbh : (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioo 0 (Tn (pidx p.2.2)))
          ∈ 𝓝 p :=
        (isOpen_Ioi.prod (isOpen_Ioo.prod isOpen_Ioo)).mem_nhds hp'
      have hev : (fun q : ℝ × ℝ × ℝ => glued g q.1 q.2.1 q.2.2)
          =ᶠ[𝓝 p] (fun q : ℝ × ℝ × ℝ => g (pidx p.2.2) q.1 q.2.1 q.2.2) := by
        filter_upwards [hnbh] with q hq
        exact hG (τ := p.2.2) (le_of_lt hτpos) q.1 q.2.1 q.2.2
          ⟨le_of_lt hq.2.2.1, le_of_lt hq.2.2.2⟩
      have hval : glued g p.1 p.2.1 p.2.2 = g (pidx p.2.2) p.1 p.2.1 p.2.2 :=
        hG (le_of_lt hτpos) p.1 p.2.1 p.2.2 ⟨le_of_lt hτpos, le_Tn_pidx p.2.2⟩
      have hmemT : (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioo 0 (Tn (pidx p.2.2)))
          ∈ 𝓝[Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioi 0] p :=
        nhdsWithin_le_nhds hnbh
      have hpiece : ContDiffWithinAt ℝ 1
          (fun q : ℝ × ℝ × ℝ => g (pidx p.2.2) q.1 q.2.1 q.2.2)
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioo 0 (Tn (pidx p.2.2))) p :=
        (hpk (pidx p.2.2)).c1.contDiffWithinAt hp'
      have hglue : ContDiffWithinAt ℝ 1
          (fun q : ℝ × ℝ × ℝ => glued g q.1 q.2.1 q.2.2)
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioo 0 (Tn (pidx p.2.2))) p :=
        hpiece.congr_of_eventuallyEq (hev.filter_mono nhdsWithin_le_nhds) hval
      exact hglue.mono_of_mem_nhdsWithin hmemT
    · -- C⁴ in space
      intro τ hτ
      rw [glued_slice hτ]
      exact (hpk (pidx τ)).c4 τ hτ (le_Tn_pidx τ)
    · -- continuity in the fake time
      intro z θ hz τ hτ
      have hmem : Set.Icc (0 : ℝ) (Tn (pidx τ)) ∈ 𝓝[Set.Ici (0 : ℝ)] τ :=
        Icc_zero_mem_nhdsWithin_Ici (lt_Tn_pidx τ)
      have hfun : (fun s => glued g z θ s) =ᶠ[𝓝[Set.Ici (0 : ℝ)] τ]
          (fun s => g (pidx τ) z θ s) := by
        filter_upwards [hmem] with τ' hτ'
        exact hG hτ z θ τ' hτ'
      have hval : glued g z θ τ = g (pidx τ) z θ τ := hG hτ z θ τ ⟨hτ, le_Tn_pidx τ⟩
      exact (((hpk (pidx τ)).cont z θ hz τ ⟨hτ, le_Tn_pidx τ⟩).mono_of_mem_nhdsWithin
        hmem).congr_of_eventuallyEq hfun hval
    · -- ℋ⁴-membership
      intro τ hτ
      rw [glued_slice hτ]
      exact (hpk (pidx τ)).mem4 τ hτ (le_Tn_pidx τ)
    · -- the ℋ³-bound on the fake-time derivative, with the shared constant
      refine Work.FTS.StrongGlobal.DbdLoc.of_local (fun S hS => ?_)
      refine ⟨g (pidx S), Cd (pidx S), fun z θ τ hτ => ?_, fun τ hτpos hτS => ?_⟩
      · rw [glued_of_nonneg hτ.1.le z θ]
        exact piece_eq_at hlim' hpk hτ.1.le (le_Tn_pidx τ)
          (le_of_lt (lt_trans hτ.2 (lt_Tn_pidx S))) z θ
      · exact (hpk (pidx S)).dbd τ hτpos (lt_trans hτS (lt_Tn_pidx S))
    · -- vanishing on the angular boundaries
      intro τ hτ z hz
      have hs : glued g z 0 τ = g (pidx τ) z 0 τ :=
        congrFun (congrFun (glued_slice (g := g) hτ) z) 0
      have hs2 : glued g z (π / 2) τ = g (pidx τ) z (π / 2) τ :=
        congrFun (congrFun (glued_slice (g := g) hτ) z) (π / 2)
      have h1 := (hpk (pidx τ)).vanish τ hτ (le_Tn_pidx τ) z hz
      exact ⟨hs.trans h1.1, hs2.trans h1.2⟩
  · -- the uniform ℋ⁴-bound
    intro τ hτ
    rw [glued_slice hτ]
    exact (hpk (pidx τ)).bd4 τ hτ (le_Tn_pidx τ)

/-- **E6 — `global_strong2` (ruling v2)**: the honest hypotheses of `exists_limH`. -/
theorem global_strong2 : ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂,
    ∀ {C₀ K Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g₀ : Fn},
    IsSmoothKernel ρ →
    (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
    EllLimOK α E → Work.FTS.VocabO2.StarPkgo2 α Cs Φs → MuLamOK α C₀ Φs E →
    EpsUniformMem α ρ Φs E g₀ C₀ K →
    ∃ g : Fam, IsDynGSolWith (Work.FTS.StrongGlobal.IsBslSolPos α) α
        (Work.FTS.Nonlin.PsiCan Φs E g) g ∧ (∀ z θ, g z θ 0 = g₀ z θ) ∧
      Work.FTS.StrongGlobal.RegPkgMin α g ∧
      ∀ τ, 0 ≤ τ → Work.FTS.Nonlin.Xn α (slice g τ) ≤ C₀ * α ^ 2 := by
  obtain ⟨α₂, hα₂, h⟩ := exists_limH
  refine ⟨α₂, hα₂, ?_⟩
  intro α hα C₀ K Ce Cs ρ Φs E g₀ hρ hEll hEL hstar hml hU
  obtain ⟨g, h1, h2, h3, h4, -⟩ := global_strong2_of_lim (h α hα hρ hEll hEL hstar hml hU)
  exact ⟨g, h1, h2, h3, h4⟩

/-- **E6 with the G2 clause exposed** — the same theorem as `global_strong2`, keeping the
`LimApprox` output of `global_strong2_of_lim`.  It is what the `StrongEps` producer of the FinalV2
conjunct (4′) consumes (`GlobalStrong2Prime.global_strong2'_proved`); `global_strong2` itself is
frozen in the ruling-v2 shape and does not carry it. -/
theorem global_strong2_g2 : ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂,
    ∀ {C₀ K Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g₀ : Fn},
    IsSmoothKernel ρ →
    (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
    EllLimOK α E → Work.FTS.VocabO2.StarPkgo2 α Cs Φs → MuLamOK α C₀ Φs E →
    EpsUniformMem α ρ Φs E g₀ C₀ K →
    ∃ g : Fam, IsDynGSolWith (Work.FTS.StrongGlobal.IsBslSolPos α) α
        (Work.FTS.Nonlin.PsiCan Φs E g) g ∧ (∀ z θ, g z θ 0 = g₀ z θ) ∧
      Work.FTS.StrongGlobal.RegPkgMin α g ∧
      (∀ τ, 0 ≤ τ → Work.FTS.Nonlin.Xn α (slice g τ) ≤ C₀ * α ^ 2) ∧
      LimApproxSE α C₀ Φs E g := by
  obtain ⟨α₂, hα₂, h⟩ := exists_limH
  exact ⟨α₂, hα₂, fun α hα C₀ K Ce Cs ρ Φs E g₀ hρ hEll hEL hstar hml hU =>
    global_strong2_of_lim (h α hα hρ hEll hEL hstar hml hU)⟩

/-! ## E6 from consistent pieces / from `ExistsLimG` (curric-46 lead install 2026-10-11)

C1–C5 ruling (`cbc/fts_strongeps_c1c5_ruling.md` §5, review fix F1 applied: `c1` is on
`Ioo 0 T`, so the `c1` clause is read inside the piece's horizon and widened by
`mono_of_mem_nhdsWithin`).  `global_strong2_of_limG` is the E6 used by
`GlobalStrong2Prime.global_strong2'_proved`; `global_strong2`/`global_strong2_g2` above stay on the
old `exists_limH` (off the `theorem_1_v2` cone). -/

/-- **E6 from consistent pieces** (generalises `Assembly.global_strong2_of_lim`: the uniqueness
clause of `ExistsLimH` was used ONLY to make the pieces agree on overlaps).  PROVED (the proof of
`global_strong2_of_lim` with `piece_eq_at` replaced by `hcons`). -/
theorem global_strong2_of_pieces {α C₀ K : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g₀ : Fn}
    {Cd : ℕ → ℝ} {g : ℕ → Fam}
    (hpk : ∀ n, EpsLimPkg α C₀ K (Cd n) (Tn n) Φs E g₀ (g n))
    (hcons : ∀ (m n : ℕ) (z θ τ : ℝ), 0 ≤ τ → τ ≤ Tn m → τ ≤ Tn n →
      g m z θ τ = g n z θ τ) :
    ∃ g : Fam, IsDynGSolWith (Work.FTS.StrongGlobal.IsBslSolPos α) α
        (Work.FTS.Nonlin.PsiCan Φs E g) g ∧ (∀ z θ, g z θ 0 = g₀ z θ) ∧
      Work.FTS.StrongGlobal.RegPkgMin α g ∧
      (∀ τ, 0 ≤ τ → Work.FTS.Nonlin.Xn α (slice g τ) ≤ C₀ * α ^ 2) ∧
      LimApproxSE α C₀ Φs E g := by
  have hG : ∀ {τ : ℝ}, 0 ≤ τ → ∀ z θ, ∀ τ' ∈ Set.Icc 0 (Tn (pidx τ)),
      glued g z θ τ' = g (pidx τ) z θ τ' := by
    intro τ _ z θ τ' hτ'
    rw [glued_of_nonneg hτ'.1 z θ]
    exact hcons _ _ z θ τ' hτ'.1 (le_Tn_pidx τ') hτ'.2
  refine ⟨glued g, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro τ hτ
      have hs : slice (g (pidx τ)) τ = slice (glued g) τ := (glued_slice hτ).symm
      exact ((hpk (pidx τ)).law τ hτ (le_Tn_pidx τ)).congr
        (Work.FTS.StrongGlobal.Ftau_congr hs) (Work.FTS.StrongGlobal.slice_PsiCan_congr hs)
    · intro z θ τ hτ hz
      have hmem : Set.Icc (0 : ℝ) (Tn (pidx τ)) ∈ 𝓝[Set.Ici (0 : ℝ)] τ :=
        Icc_zero_mem_nhdsWithin_Ici (lt_Tn_pidx τ)
      have hfun : (fun s => glued g z θ s) =ᶠ[𝓝[Set.Ici (0 : ℝ)] τ]
          (fun s => g (pidx τ) z θ s) := by
        filter_upwards [hmem] with τ' hτ'
        exact hG hτ z θ τ' hτ'
      have hval : glued g z θ τ = g (pidx τ) z θ τ := hG hτ z θ τ ⟨hτ, le_Tn_pidx τ⟩
      have hgoal := (((hpk (pidx τ)).eqT τ hτ (le_Tn_pidx τ) z θ hz).mono_of_mem_nhdsWithin
        hmem).congr_of_eventuallyEq hfun hval
      show HasDerivWithinAt (fun s => glued g z θ s) (rhsFun α Φs E (glued g) τ z θ)
        (Set.Ici (0 : ℝ)) τ
      rw [rhsFun_congr (glued_slice hτ)]
      exact hgoal
  · intro z θ
    rw [glued_of_nonneg le_rfl]
    exact (hpk (pidx 0)).init z θ
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      have hτpos : 0 < p.2.2 := hp.2.2
      have hp' : p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioo 0 (Tn (pidx p.2.2)) :=
        ⟨hp.1, hp.2.1, hτpos, lt_Tn_pidx p.2.2⟩
      have hnbh : (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioo 0 (Tn (pidx p.2.2)))
          ∈ 𝓝 p :=
        (isOpen_Ioi.prod (isOpen_Ioo.prod isOpen_Ioo)).mem_nhds hp'
      have hev : (fun q : ℝ × ℝ × ℝ => glued g q.1 q.2.1 q.2.2)
          =ᶠ[𝓝 p] (fun q : ℝ × ℝ × ℝ => g (pidx p.2.2) q.1 q.2.1 q.2.2) := by
        filter_upwards [hnbh] with q hq
        exact hG (τ := p.2.2) (le_of_lt hτpos) q.1 q.2.1 q.2.2
          ⟨le_of_lt hq.2.2.1, le_of_lt hq.2.2.2⟩
      have hval : glued g p.1 p.2.1 p.2.2 = g (pidx p.2.2) p.1 p.2.1 p.2.2 :=
        hG (le_of_lt hτpos) p.1 p.2.1 p.2.2 ⟨le_of_lt hτpos, le_Tn_pidx p.2.2⟩
      have hmemT : (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioo 0 (Tn (pidx p.2.2)))
          ∈ 𝓝[Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioi 0] p :=
        nhdsWithin_le_nhds hnbh
      exact (((hpk (pidx p.2.2)).c1.contDiffWithinAt hp').congr_of_eventuallyEq
        (hev.filter_mono nhdsWithin_le_nhds) hval).mono_of_mem_nhdsWithin hmemT
    · intro τ hτ
      rw [glued_slice hτ]
      exact (hpk (pidx τ)).c4 τ hτ (le_Tn_pidx τ)
    · intro z θ hz τ hτ
      have hmem : Set.Icc (0 : ℝ) (Tn (pidx τ)) ∈ 𝓝[Set.Ici (0 : ℝ)] τ :=
        Icc_zero_mem_nhdsWithin_Ici (lt_Tn_pidx τ)
      have hfun : (fun s => glued g z θ s) =ᶠ[𝓝[Set.Ici (0 : ℝ)] τ]
          (fun s => g (pidx τ) z θ s) := by
        filter_upwards [hmem] with τ' hτ'
        exact hG hτ z θ τ' hτ'
      have hval : glued g z θ τ = g (pidx τ) z θ τ := hG hτ z θ τ ⟨hτ, le_Tn_pidx τ⟩
      exact (((hpk (pidx τ)).cont z θ hz τ ⟨hτ, le_Tn_pidx τ⟩).mono_of_mem_nhdsWithin
        hmem).congr_of_eventuallyEq hfun hval
    · intro τ hτ
      rw [glued_slice hτ]
      exact (hpk (pidx τ)).mem4 τ hτ (le_Tn_pidx τ)
    · refine Work.FTS.StrongGlobal.DbdLoc.of_local (fun S hS => ?_)
      refine ⟨g (pidx S), Cd (pidx S), fun z θ τ hτ => ?_, fun τ hτpos hτS => ?_⟩
      · rw [glued_of_nonneg hτ.1.le z θ]
        exact hcons _ _ z θ τ hτ.1.le (le_Tn_pidx τ)
          (le_of_lt (lt_trans hτ.2 (lt_Tn_pidx S)))
      · exact (hpk (pidx S)).dbd τ hτpos (lt_trans hτS (lt_Tn_pidx S))
    · intro τ hτ z hz
      have hs : glued g z 0 τ = g (pidx τ) z 0 τ :=
        congrFun (congrFun (glued_slice (g := g) hτ) z) 0
      have hs2 : glued g z (π / 2) τ = g (pidx τ) z (π / 2) τ :=
        congrFun (congrFun (glued_slice (g := g) hτ) z) (π / 2)
      have h1 := (hpk (pidx τ)).vanish τ hτ (le_Tn_pidx τ) z hz
      exact ⟨hs.trans h1.1, hs2.trans h1.2⟩
  · intro τ hτ
    rw [glued_slice hτ]
    exact (hpk (pidx τ)).bd4 τ hτ (le_Tn_pidx τ)
  · intro T hT
    obtain ⟨N, hN⟩ : ∃ N : ℕ, T ≤ Tn N :=
      ⟨Nat.ceil T, by
        have h := Nat.le_ceil T
        simp only [Tn]
        push_cast
        linarith⟩
    obtain ⟨gn, B, L, hb, hlip, hjet, hmu⟩ := (hpk N).limApprox T hT hN
    have hs : ∀ {τ : ℝ}, τ ∈ Set.Icc (0 : ℝ) T → ∀ z' θ', glued g z' θ' τ = g N z' θ' τ := by
      intro τ hτ z' θ'
      rw [glued_of_nonneg hτ.1 z' θ']
      exact hcons _ _ z' θ' τ hτ.1 (le_Tn_pidx τ) (le_trans hτ.2 hN)
    have hsSlice : ∀ {τ : ℝ}, τ ∈ Set.Icc (0 : ℝ) T → slice (glued g) τ = slice (g N) τ := by
      intro τ hτ
      funext z' θ'
      simp only [slice]
      exact hs hτ z' θ'
    refine ⟨gn, B, L, hb, hlip, ?_, ?_⟩
    · intro τ hτ j i hji z θ hzθ
      rw [hsSlice hτ]
      exact hjet τ hτ j i hji z θ hzθ
    · intro τ hτ
      have hPsi : slice (Work.FTS.Nonlin.PsiCan Φs E (glued g)) τ
          = slice (Work.FTS.Nonlin.PsiCan Φs E (g N)) τ := by
        funext z' θ'
        simp only [Work.FTS.Nonlin.PsiCan, slice]
        rw [hsSlice hτ]
      have hF : Work.Construction.Ftau α (glued g) τ = Work.Construction.Ftau α (g N) τ := by
        funext z' θ'
        simp only [Work.Construction.Ftau]
        rw [hs hτ z' θ']
      have hmuEq : Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (glued g))
            (glued g) τ
          = Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (g N)) (g N) τ := by
        simp only [Work.FTS.Galerkin.muDyn]
        rw [hF, hsSlice hτ, hPsi]
      rw [hmuEq]
      exact hmu τ hτ

/-- **E6 from the uniqueness-free E5 conclusion.**  PROVED: constant pieces are consistent. -/
theorem global_strong2_of_limG {α C₀ K : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g₀ : Fn}
    (hlim : ExistsLimG α C₀ K Φs E g₀) :
    ∃ g : Fam, IsDynGSolWith (Work.FTS.StrongGlobal.IsBslSolPos α) α
        (Work.FTS.Nonlin.PsiCan Φs E g) g ∧ (∀ z θ, g z θ 0 = g₀ z θ) ∧
      Work.FTS.StrongGlobal.RegPkgMin α g ∧
      (∀ τ, 0 ≤ τ → Work.FTS.Nonlin.Xn α (slice g τ) ≤ C₀ * α ^ 2) ∧
      LimApproxSE α C₀ Φs E g := by
  obtain ⟨g, hg⟩ := hlim
  choose Cd _hCd hpk using fun n : ℕ => hg (Tn n) (Tn_pos n)
  exact global_strong2_of_pieces (g := fun _ => g) hpk (fun _ _ _ _ _ _ _ _ => rfl)

/-- The old E5 conclusion still feeds the new E6 (so the refactor is backward-compatible). -/
theorem global_strong2_of_lim' {α C₀ K : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g₀ : Fn}
    (hlim : ExistsLimH α C₀ K Φs E g₀) :
    ∃ g : Fam, IsDynGSolWith (Work.FTS.StrongGlobal.IsBslSolPos α) α
        (Work.FTS.Nonlin.PsiCan Φs E g) g ∧ (∀ z θ, g z θ 0 = g₀ z θ) ∧
      Work.FTS.StrongGlobal.RegPkgMin α g ∧
      (∀ τ, 0 ≤ τ → Work.FTS.Nonlin.Xn α (slice g τ) ≤ C₀ * α ^ 2) ∧
      LimApproxSE α C₀ Φs E g := by
  choose Cd _hCdpos g hpk _huniq using fun n : ℕ => hlim (Tn n) (Tn_pos n)
  exact global_strong2_of_pieces hpk
    (fun m n z θ τ hτ hm hn => piece_eq_at hlim hpk hτ hm hn z θ)

end Work.FTS.StrongEps
