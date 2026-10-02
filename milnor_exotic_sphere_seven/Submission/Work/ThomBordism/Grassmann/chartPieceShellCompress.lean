import Mathlib
import Submission.Work.ThomBordism.Grassmann.thomSpacePieces
import Submission.Work.ThomBordism.Grassmann.Torsion.ModelGeom
import Submission.Work.ThomBordism.TwoSet.CompressBasic
import Submission.Work.ThomBordism.TwoSet.Assembly
import Submission.Work.RatHurewicz.compression_of_relPiVanishing
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.Stems.sphereConnectivity
import Submission.Work.ThomBordism.Grassmann.ClosedPiece.fibreCompress

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The shell over a chart cell compresses into the far part

**Target** (`Work.ThomBordism.Grassmann.chartPieceShellCompress`): for `k m : ℕ`, a chart
`S₀ : ChartIdx k m` and an open `W ⊆ (tautologicalBundle k m).baseSet S₀`,

    Compress ↥(π⁻¹W) {p | 1 < fibN p} j        for every `j < k`,

i.e. every map of pairs `(I^j, ∂I^j) → (π⁻¹W, {fibN > 1})` is homotopic, relative to the boundary,
into the shell `{fibN > 1}`.  This is the "shell" (total space over the chart cell) version of the
compression of the closed piece `{∞} ∪ π⁻¹W`, and the compression form of the vanishing of the
relative homotopy groups `π_e(π⁻¹W, {fibN > 1})` for `e < k`.

## Route

The bundle is trivial over the chart, so `π⁻¹W ≃ₜ ↥W × ℝ^k` (`Bundle.Trivialization.preimageHomeomorph`);
under this homeomorphism the zero section corresponds to `{q | q.2 = 0}`, so the *punctured*
compression statement for `↥W × ℝ^k` (`Work.ThomBordism.Grassmann.ClosedPiece.fibreCompress`, proved
from the connectivity of spheres) transfers to the shell:

    `Compress ↥(π⁻¹W) {p | fibN p ≠ 0} j`      (`shellPuncturedCompress`, `Compress.of_homeo`).

A map into the punctured part whose *boundary* already lies in the shell can then be pushed into the
shell by rescaling the fibre coordinate by a continuous factor which is `1` on the boundary and
large on the compact part of the image where `fibN ≤ 1` (`escapeShell`, the total-space analogue of
`Work.ThomBordism.Grassmann.escape_to_far`).  Concatenating the two homotopies gives the target.

## Main declarations

* `TwoSet.Compress.of_homeo` — transfer of the compression property along a homeomorphism of pairs;
* `Work.ThomBordism.Grassmann.escapeShell` — the escape to the shell;
* `Work.ThomBordism.Grassmann.shellPuncturedCompress`;
* `Work.ThomBordism.Grassmann.chartPieceShellCompress`.
-/

open scoped Topology unitInterval
open Work.TangentClasses

namespace Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-! ## Transfer of the compression property along a homeomorphism of pairs -/

/-- **The compression property transfers along a homeomorphism of pairs.**  If `e : X ≃ₜ Y` carries
`A ⊆ X` onto `B ⊆ Y` and the pair `(Y, B)` has the compression property in dimension `d`, then so
does `(X, A)`. -/
theorem TwoSet.Compress.of_homeo {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {A : Set X} {B : Set Y} (hAB : ∀ x, e x ∈ B ↔ x ∈ A) {d : ℕ}
    (h : TwoSet.Compress Y B d) : TwoSet.Compress X A d := by
  intro f hf
  have hfB : ∀ x, x ∈ Cube.boundary (Fin d) → e (f x) ∈ B :=
    fun x hx => (hAB (f x)).mpr (hf x hx)
  obtain ⟨G, hG0, hGbd, hG1⟩ := h ⟨fun x => e (f x), e.continuous.comp f.continuous⟩ hfB
  refine ⟨⟨fun p => e.symm (G p), e.symm.continuous.comp G.continuous⟩, ?_, ?_, ?_⟩
  · intro x
    show e.symm (G (x, 0)) = f x
    rw [hG0 x]
    exact e.symm_apply_apply (f x)
  · intro x hx t
    show e.symm (G (x, t)) = f x
    rw [hGbd x hx t]
    exact e.symm_apply_apply (f x)
  · intro x
    show e.symm (G (x, 1)) ∈ A
    rw [← hAB (e.symm (G (x, 1))), e.apply_symm_apply]
    exact hG1 x

/-! ## The punctured part of the total space over a chart cell -/

/-- **The punctured shell compresses below the fibre dimension.**  For `W ⊆ baseSet S₀` and `j < k`,
every map of pairs `(I^j, ∂I^j) → (π⁻¹W, {fibN ≠ 0})` is homotopic, relative to the boundary, into
the punctured part `{fibN ≠ 0}`.

This is `Work.ThomBordism.Grassmann.ClosedPiece.fibreCompress` (the pair `(X × ℝ^k, X × (ℝ^k∖0))`
has the compression property in dimensions `d` with `d + 1 ≤ k`), transported along the chart
homeomorphism `π⁻¹W ≃ₜ ↥W × ℝ^k`. -/
theorem shellPuncturedCompress (k m : ℕ) (S₀ : ChartIdx k m) (W : Set (OG k m))
    (hWsub : W ⊆ (tautologicalBundle k m).baseSet S₀) :
    ∀ j : ℕ, j < k →
      TwoSet.Compress ↥((tautologicalBundle k m).proj ⁻¹' W)
        {p : ↥((tautologicalBundle k m).proj ⁻¹' W) |
          Torsion.fibN k m (p : (tautologicalBundle k m).TotalSpace) ≠ 0} j := by
  intro j hj
  have hbaseSet : W ⊆ ((tautologicalBundle k m).localTriv S₀).baseSet := by
    intro x hx
    show x ∈ (tautologicalBundle k m).baseSet S₀
    exact hWsub hx
  have hprod : TwoSet.Compress (↥W × Amb k) {q : ↥W × Amb k | q.2 ≠ 0} j :=
    ClosedPiece.fibreCompress ↥W k j hj
  refine TwoSet.Compress.of_homeo
    (((tautologicalBundle k m).localTriv S₀).preimageHomeomorph hbaseSet) ?_ hprod
  intro x
  have hbS : (x : Torsion.TM k m).proj ∈ (tautologicalBundle k m).baseSet S₀ := hWsub x.2
  have h1 : ((tautologicalBundle k m).localTriv S₀ (x : Torsion.TM k m)).2 ≠ 0 ↔
      Torsion.fibN k m (x : Torsion.TM k m) ≠ 0 := by
    rw [ne_eq, ne_eq, localTriv_snd_eq_zero (tautologicalBundle k m) S₀ (x : Torsion.TM k m) hbS,
      Torsion.fibN_eq_zero_iff]
    try exact Iff.rfl
  rw [Bundle.Trivialization.preimageHomeomorph_apply]
  simpa only [Set.mem_ofPred_eq] using h1

/-! ## The escape to the shell -/

/-- **Escape to the shell.**  A continuous map `g` from `I^j` into the part of the total space
sitting over `W`, whose image avoids the zero section (`fibN ≠ 0`) and whose boundary values already
lie in the shell `{fibN > 1}`, is homotopic relative to the boundary into the shell.

The homotopy rescales the fibre coordinate by the continuous factor
`φ(x,t) = 1 + t · η(x) · 2 / fibN (g x)`, where the Urysohn function `η` is `1` on the compact set
`{x | fibN (g x) ≤ 1}` and `0` on `∂I^j`: it fixes `g` at `t = 0` and on the boundary, leaves the
base points unchanged, and at `t = 1` multiplies `fibN` by `1 + η(x)·2/fibN (g x)`, i.e. adds
`2·η(x) ≥ 0` on the nose, which pushes `{fibN ≤ 1}` out of the disc and leaves `{fibN > 1}`
untouched. -/
theorem escapeShell (k m : ℕ) (W : Set (OG k m)) {j : ℕ}
    (g : C(TwoSet.IC j, ↥((tautologicalBundle k m).proj ⁻¹' W)))
    (hg : ∀ x, Torsion.fibN k m (g x : Torsion.TM k m) ≠ 0)
    (hbd : ∀ x, x ∈ Cube.boundary (Fin j) → 1 < Torsion.fibN k m (g x : Torsion.TM k m)) :
    ∃ G : C(TwoSet.IC j × I, ↥((tautologicalBundle k m).proj ⁻¹' W)),
      (∀ x, G (x, 0) = g x) ∧
      (∀ x, x ∈ Cube.boundary (Fin j) → ∀ t, G (x, t) = g x) ∧
      (∀ x, 1 < Torsion.fibN k m (G (x, 1) : Torsion.TM k m)) := by
  classical
  set K : Set (TwoSet.IC j) := {x | Torsion.fibN k m (g x : Torsion.TM k m) ≤ 1} with hK
  have hNcont : Continuous fun x : TwoSet.IC j => Torsion.fibN k m (g x : Torsion.TM k m) :=
    (Torsion.fibN_continuous k m).comp (continuous_subtype_val.comp g.continuous)
  have hKclosed : IsClosed K := isClosed_le hNcont continuous_const
  have hdisj : Disjoint (Cube.boundary (Fin j) : Set (TwoSet.IC j)) K := by
    refine Set.disjoint_left.mpr fun x hxb hxK => ?_
    have hx1 : 1 < Torsion.fibN k m (g x : Torsion.TM k m) := hbd x hxb
    have hx2 : Torsion.fibN k m (g x : Torsion.TM k m) ≤ 1 := hxK
    linarith
  obtain ⟨η, hη0, hη1, hηrange⟩ :=
    exists_continuous_zero_one_of_isClosed (TwoSet.isClosed_cubeBoundary j) hKclosed hdisj
  have hη01 : ∀ x : TwoSet.IC j, 0 ≤ (η x : ℝ) ∧ (η x : ℝ) ≤ 1 := fun x =>
    Set.mem_Icc.mp (hηrange x)
  have hNpos : ∀ x : TwoSet.IC j, 0 < Torsion.fibN k m (g x : Torsion.TM k m) := fun x =>
    lt_of_le_of_ne (Torsion.fibN_nonneg k m (g x : Torsion.TM k m)) (Ne.symm (hg x))
  -- the continuous family of rescaling factors
  set Φ : C(TwoSet.IC j × I, ℝ) :=
    ⟨fun p => 1 + (p.2 : ℝ) * (η p.1 : ℝ) *
        (2 * (Torsion.fibN k m (g p.1 : Torsion.TM k m))⁻¹), by
      have h1 : Continuous fun p : TwoSet.IC j × I =>
          (Torsion.fibN k m (g p.1 : Torsion.TM k m))⁻¹ :=
        (hNcont.comp continuous_fst).inv₀ (fun p => hg p.1)
      have h2 : Continuous fun p : TwoSet.IC j × I => (η p.1 : ℝ) := by
        fun_prop
      have h3 : Continuous fun p : TwoSet.IC j × I => (p.2 : ℝ) :=
        continuous_subtype_val.comp continuous_snd
      exact continuous_const.add ((h3.mul h2).mul (continuous_const.mul h1))⟩ with hΦdef
  have hΦpos : ∀ p : TwoSet.IC j × I, 1 ≤ Φ p := by
    intro p
    have hηnn : 0 ≤ (η p.1 : ℝ) := (hη01 p.1).1
    have ht : 0 ≤ (p.2 : ℝ) := p.2.2.1
    have hN : 0 < Torsion.fibN k m (g p.1 : Torsion.TM k m) := hNpos p.1
    have hterm : 0 ≤ (p.2 : ℝ) * (η p.1 : ℝ) *
        (2 * (Torsion.fibN k m (g p.1 : Torsion.TM k m))⁻¹) :=
      mul_nonneg (mul_nonneg ht hηnn) (le_of_lt (by positivity))
    show 1 ≤ 1 + (p.2 : ℝ) * (η p.1 : ℝ) *
        (2 * (Torsion.fibN k m (g p.1 : Torsion.TM k m))⁻¹)
    linarith
  -- the underlying map of the homotopy
  have hmain : Continuous fun p : TwoSet.IC j × I =>
      (⟨(g p.1 : Torsion.TM k m).1, Φ p • (g p.1 : Torsion.TM k m).2⟩ : Torsion.TM k m) :=
    Work.Thom.continuous_smul_section (tautologicalBundle k m)
      ⟨fun p : TwoSet.IC j × I => (g p.1 : Torsion.TM k m),
        continuous_subtype_val.comp (g.continuous.comp continuous_fst)⟩ Φ
  set Hfun : TwoSet.IC j × I → ↥((tautologicalBundle k m).proj ⁻¹' W) :=
    fun p => ⟨⟨(g p.1 : Torsion.TM k m).1, Φ p • (g p.1 : Torsion.TM k m).2⟩, (g p.1).2⟩
    with hHdef
  have hHcont : Continuous Hfun := by
    refine Continuous.subtype_mk ?_ _
    simpa only [hHdef] using hmain
  refine ⟨⟨Hfun, hHcont⟩, ?_, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    have h0 : Φ (x, 0) = 1 := by
      show 1 + (((0 : I) : ℝ)) * (η x : ℝ) * _ = 1
      rw [show (((0 : I) : ℝ)) = 0 from rfl]
      ring
    show (⟨(g x : Torsion.TM k m).1, Φ (x, 0) • (g x : Torsion.TM k m).2⟩ : Torsion.TM k m)
      = (g x : Torsion.TM k m)
    rw [h0, one_smul]
  · intro x hx t
    apply Subtype.ext
    have hηx : (η x : ℝ) = 0 := by
      rw [hη0 hx]
      rfl
    have h1 : Φ (x, t) = 1 := by
      show 1 + (t : ℝ) * (η x : ℝ) * _ = 1
      rw [hηx]
      ring
    show (⟨(g x : Torsion.TM k m).1, Φ (x, t) • (g x : Torsion.TM k m).2⟩ : Torsion.TM k m)
      = (g x : Torsion.TM k m)
    rw [h1, one_smul]
  · intro x
    have hN := hNpos x
    have h1 : Φ (x, 1) = 1 + (η x : ℝ) *
        (2 * (Torsion.fibN k m (g x : Torsion.TM k m))⁻¹) := by
      show 1 + (((1 : I) : ℝ)) * (η x : ℝ) * _ = 1 + (η x : ℝ) * _
      rw [show (((1 : I) : ℝ)) = 1 from rfl, one_mul]
    have hsm : Torsion.fibN k m
        (⟨(g x : Torsion.TM k m).1, Φ (x, 1) • (g x : Torsion.TM k m).2⟩ : Torsion.TM k m)
        = Φ (x, 1) * Torsion.fibN k m (g x : Torsion.TM k m) :=
      Torsion.fibN_smul k m (le_trans zero_le_one (hΦpos (x, 1))) (g x : Torsion.TM k m)
    have key : Φ (x, 1) * Torsion.fibN k m (g x : Torsion.TM k m)
        = Torsion.fibN k m (g x : Torsion.TM k m) + 2 * (η x : ℝ) := by
      rw [h1]
      have hNne : Torsion.fibN k m (g x : Torsion.TM k m) ≠ 0 := ne_of_gt hN
      field_simp
    show 1 < Torsion.fibN k m
      (⟨(g x : Torsion.TM k m).1, Φ (x, 1) • (g x : Torsion.TM k m).2⟩ : Torsion.TM k m)
    rw [hsm, key]
    by_cases hxK : x ∈ K
    · have hηx : (η x : ℝ) = 1 := by
        rw [hη1 hxK]
        rfl
      rw [hηx]
      linarith [Torsion.fibN_nonneg k m (g x : Torsion.TM k m)]
    · have hgt : 1 < Torsion.fibN k m (g x : Torsion.TM k m) := by
        by_contra hle
        exact hxK (le_of_not_gt hle)
      have hηnn : 0 ≤ (η x : ℝ) := (hη01 x).1
      linarith

/-! ## The target -/

theorem chartPieceShellCompress (k m : ℕ) (S₀ : ChartIdx k m) (W : Set (OG k m))
    (hW : IsOpen W) (hWsub : W ⊆ (tautologicalBundle k m).baseSet S₀) :
    ∀ j : ℕ, j < k →
      Work.ThomBordism.TwoSet.Compress ↥((tautologicalBundle k m).proj ⁻¹' W)
        {p : ↥((tautologicalBundle k m).proj ⁻¹' W) |
          1 < Torsion.fibN k m (p : (tautologicalBundle k m).TotalSpace)} j := by
  intro j hj
  have hstep1 : TwoSet.Compress ↥((tautologicalBundle k m).proj ⁻¹' W)
      {p : ↥((tautologicalBundle k m).proj ⁻¹' W) |
        Torsion.fibN k m (p : Torsion.TM k m) ≠ 0} j :=
    shellPuncturedCompress k m S₀ W hWsub j hj
  intro f hf
  have hfP : ∀ x, x ∈ Cube.boundary (Fin j) →
      f x ∈ {p : ↥((tautologicalBundle k m).proj ⁻¹' W) |
        Torsion.fibN k m (p : Torsion.TM k m) ≠ 0} := fun x hx =>
      ne_of_gt (lt_trans zero_lt_one (show 1 < Torsion.fibN k m (f x : Torsion.TM k m) from hf x hx))
  obtain ⟨G₁, hG₁0, hG₁bd, hG₁1⟩ := hstep1 f hfP
  -- the endpoint of the first homotopy, which avoids the zero section
  set g : C(TwoSet.IC j, ↥((tautologicalBundle k m).proj ⁻¹' W)) :=
    ⟨fun x => G₁ (x, 1), G₁.continuous.comp (continuous_id.prodMk continuous_const)⟩ with hgdef
  have hg : ∀ x, Torsion.fibN k m (g x : Torsion.TM k m) ≠ 0 := fun x => hG₁1 x
  have hgbd : ∀ x, x ∈ Cube.boundary (Fin j) →
      1 < Torsion.fibN k m (g x : Torsion.TM k m) := by
    intro x hx
    have h1 : g x = f x := by
      show G₁ (x, 1) = f x
      exact hG₁bd x hx 1
    rw [h1]
    exact hf x hx
  obtain ⟨G₂, hG₂0, hG₂bd, hG₂1⟩ := escapeShell k m W g hg hgbd
  -- concatenate the two homotopies
  set Gfun : TwoSet.IC j × I → ↥((tautologicalBundle k m).proj ⁻¹' W) :=
    fun p => if (2 : ℝ) * (p.2 : ℝ) ≤ 1
      then G₁ (p.1, Work.RatHurewicz.clampI (2 * (p.2 : ℝ)))
      else G₂ (p.1, Work.RatHurewicz.clampI (2 * (p.2 : ℝ) - 1)) with hGfun
  have hseam : ∀ p : TwoSet.IC j × I, (2 : ℝ) * (p.2 : ℝ) = 1 →
      G₁ (p.1, Work.RatHurewicz.clampI (2 * (p.2 : ℝ))) =
        G₂ (p.1, Work.RatHurewicz.clampI (2 * (p.2 : ℝ) - 1)) := by
    intro p hp
    have h1 : Work.RatHurewicz.clampI (2 * (p.2 : ℝ)) = (1 : I) := by
      rw [hp, Work.RatHurewicz.clampI_one']
    have h2 : Work.RatHurewicz.clampI (2 * (p.2 : ℝ) - 1) = (0 : I) := by
      rw [show 2 * (p.2 : ℝ) - 1 = 0 from by rw [hp]; norm_num,
        Work.RatHurewicz.clampI_zero']
    rw [h1, h2]
    exact (hG₂0 p.1).symm
  have hGfun_le : ∀ p : TwoSet.IC j × I, (2 : ℝ) * (p.2 : ℝ) ≤ 1 →
      Gfun p = G₁ (p.1, Work.RatHurewicz.clampI (2 * (p.2 : ℝ))) := by
    intro p hp
    simp only [hGfun]
    exact if_pos hp
  have hGfun_gt : ∀ p : TwoSet.IC j × I, ¬ (2 : ℝ) * (p.2 : ℝ) ≤ 1 →
      Gfun p = G₂ (p.1, Work.RatHurewicz.clampI (2 * (p.2 : ℝ) - 1)) := by
    intro p hp
    simp only [hGfun]
    exact if_neg hp
  have hGcont : Continuous Gfun := by
    simp only [hGfun]
    refine Continuous.if_le ?_ ?_ ?_ ?_ hseam
    · exact G₁.continuous.comp
        (continuous_fst.prodMk (Work.RatHurewicz.continuous_clampI.comp
          (continuous_const.mul (continuous_subtype_val.comp continuous_snd))))
    · exact G₂.continuous.comp
        (continuous_fst.prodMk (Work.RatHurewicz.continuous_clampI.comp
          ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).sub
            continuous_const)))
    · exact continuous_const.mul (continuous_subtype_val.comp continuous_snd)
    · exact continuous_const
  refine ⟨⟨Gfun, hGcont⟩, ?_, ?_, ?_⟩
  · intro x
    show Gfun (x, 0) = f x
    rw [hGfun_le (x, 0) (by norm_num)]
    rw [show (2 : ℝ) * (((0 : I) : ℝ)) = 0 from by norm_num, Work.RatHurewicz.clampI_zero']
    exact hG₁0 x
  · intro x hx t
    show Gfun (x, t) = f x
    by_cases h : (2 : ℝ) * (t : ℝ) ≤ 1
    · rw [hGfun_le (x, t) h]
      exact hG₁bd x hx _
    · rw [hGfun_gt (x, t) h]
      rw [hG₂bd x hx _]
      exact hG₁bd x hx 1
  · intro x
    show Gfun (x, 1) ∈ {p : ↥((tautologicalBundle k m).proj ⁻¹' W) |
      1 < Torsion.fibN k m (p : Torsion.TM k m)}
    rw [hGfun_gt (x, 1) (by norm_num)]
    rw [show 2 * (((1 : I) : ℝ)) - 1 = 1 from by norm_num,
      Work.RatHurewicz.clampI_one']
    exact hG₂1 x

end

end Work.ThomBordism.Grassmann
