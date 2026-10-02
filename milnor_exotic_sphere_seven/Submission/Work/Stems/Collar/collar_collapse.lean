import Mathlib
import Submission.Work.Stems.Collar.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The double collar collapses onto the identity

`Submission.Work.Stems.Collar.Defs` builds, for a path `p : Path x y`, the "collar" map
`collar p : Ω^M X x → Ω^M X y`, which fills the collar `{delta ≤ 1/4}` of the cube with `p`
and shrinks the loop `f` into the inner cube.

The present file proves that the composite `collar p.symm ∘ collar p` is homotopic to the
identity of `Ω^M X x` (the statement `Work.Stems.Collar.collar_collapse`).  Geometrically the
composite walks *out* along `p` and *back* along `p` in the collar of the cube and applies a
doubly shrunk copy of `f` in the middle; the homotopy contracts the loop `p · p̄` and expands
the inner copy of `f` back to the whole cube.

The proof is organised as a chain of three homotopies of maps `Ω^M X x → Ω^M X x`:

* `Phi ≃ A` (contraction of the path part; `H1`)
* `A ≃ B`  (the "constant collar" `{delta ≤ 3/8} ↦ x` shrinks to nothing; `H2`)
* `B ≃ id` (the reparametrisation `sigma 1/4 ∘ sigma 1/4` of the cube is homotopic to `id`; `H3`)

where
`A f t = if delta t ≤ 3/8 then x else f (sigma 1/4 (sigma 1/4 t))` and
`B f t = f (sigma 1/4 (sigma 1/4 t))`.
-/

open scoped Topology unitInterval Topology.Homotopy
open Set Function

namespace Work.Stems.Collar

variable {M : Type*} [Fintype M] [Nonempty M]
variable {X : Type*} [TopologicalSpace X] {x y : X}

/-! ## Elementary facts about `scale`, `sigma` and `delta` at the collar radius `1/4` -/

theorem coe_scale_quarter (u : I) :
    ((scale (1 / 4) u : I) : ℝ) = max 0 (min 1 (2 * (u : ℝ) - 1 / 2)) := by
  rw [coe_scale]
  have h : (1 : ℝ) - 2 * (1 / 4) = 1 / 2 := by norm_num
  rw [h]
  have h2 : ((u : ℝ) - 1 / 4) / (1 / 2) = 2 * (u : ℝ) - 1 / 2 := by field_simp; ring
  rw [h2]

theorem scale_quarter_le_iff (u : I) :
    ((scale (1 / 4) u : I) : ℝ) ≤ 1 / 4 ↔ (u : ℝ) ≤ 3 / 8 := by
  rw [coe_scale_quarter, max_le_iff, min_le_iff, sub_le_iff_le_add]
  constructor
  · rintro ⟨-, h | h⟩ <;> linarith
  · intro h; exact ⟨by norm_num, Or.inr (by linarith)⟩

theorem le_scale_quarter_iff (u : I) :
    3 / 4 ≤ ((scale (1 / 4) u : I) : ℝ) ↔ 5 / 8 ≤ (u : ℝ) := by
  rw [coe_scale_quarter, le_max_iff, le_min_iff]
  constructor
  · rintro (h | ⟨-, h⟩) <;> linarith
  · intro h; exact Or.inr ⟨by norm_num, by linarith⟩

/-- The crucial "radial" identity: a point lies in the collar of `sigma 1/4` exactly when it
lies in the collar of width `3/8` of the cube. -/
theorem delta_sigma_quarter_iff (t : M → I) :
    delta (sigma (1 / 4) t) ≤ 1 / 4 ↔ delta t ≤ 3 / 8 := by
  have h : ∀ j : M, (((sigma (1 / 4) t) j : I) : ℝ) ≤ 1 / 4 ↔ (t j : ℝ) ≤ 3 / 8 := by
    intro j; rw [sigma_apply]; exact scale_quarter_le_iff (t j)
  have h2 : ∀ j : M, (3 / 4 : ℝ) ≤ (((sigma (1 / 4) t) j : I) : ℝ) ↔ 5 / 8 ≤ (t j : ℝ) := by
    intro j; rw [sigma_apply]; exact le_scale_quarter_iff (t j)
  rw [delta_le_iff, show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num]
  rw [delta_le_iff, show (1 : ℝ) - 3 / 8 = 5 / 8 by norm_num]
  exact exists_congr (fun j => or_congr (h j) (h2 j))

theorem sigma_sigma_mem_boundary_of_delta_le {t : M → I} (h : delta t ≤ 3 / 8) :
    sigma (1 / 4) (sigma (1 / 4) t) ∈ Cube.boundary M :=
  sigma_mem_boundary_of_delta_le (by norm_num) ((delta_sigma_quarter_iff t).mpr h)

theorem clamp01_coe (s : I) : clamp01 (s : ℝ) = s := by
  rw [clamp01_of_mem s.2]

theorem delta_sigma_eq_zero_of_delta_le_quarter {t : M → I} (h : delta t ≤ 1 / 4) :
    delta (sigma (1 / 4) t) = 0 :=
  (delta_eq_zero_iff).mpr (sigma_mem_boundary_of_delta_le (by norm_num) h)

/-- `sigma w` maps the boundary of the cube to itself, for `0 ≤ w < 1/2`. -/
theorem sigma_mem_boundary {w : ℝ} (h0 : 0 ≤ w) (h1 : w < 1 / 2) {t : M → I}
    (ht : t ∈ Cube.boundary M) : sigma w t ∈ Cube.boundary M := by
  obtain ⟨j, hj | hj⟩ := ht
  · exact ⟨j, Or.inl (by
      rw [sigma_apply, hj]
      exact (scale_eq_zero_iff h1 0).mpr h0)⟩
  · exact ⟨j, Or.inr (by
      rw [sigma_apply, hj]
      exact (scale_eq_one_iff h1 1).mpr (by norm_num; exact h0))⟩

theorem sigma_quarter_mem_boundary {t : M → I} (ht : t ∈ Cube.boundary M) :
    sigma (1 / 4) t ∈ Cube.boundary M :=
  sigma_mem_boundary (by norm_num) (by norm_num) ht

theorem symm_clamp01 (r : ℝ) : unitInterval.symm (clamp01 r) = clamp01 (1 - r) := by
  apply Subtype.ext
  rw [unitInterval.coe_symm_eq, coe_clamp01, coe_clamp01]
  rcases le_total r 1 with h1 | h1
  · rcases le_total 0 r with h0 | h0
    · rw [min_eq_right h1, max_eq_right h0, min_eq_right (by linarith),
        max_eq_right (by linarith)]
    · rw [min_eq_right (by linarith), max_eq_left h0,
        min_eq_left (by linarith : (1 : ℝ) ≤ 1 - r), max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
      norm_num
  · rw [min_eq_left h1, max_eq_right (by norm_num : (0 : ℝ) ≤ 1),
      min_eq_right (by linarith : 1 - r ≤ 1), max_eq_left (by linarith : 1 - r ≤ 0)]
    norm_num

theorem path_symm_apply (p : Path x y) (u : I) : p.symm u = p (unitInterval.symm u) := by
  rw [Path.symm_apply]; rfl

theorem path_symm_clamp01 (p : Path x y) (r : ℝ) :
    p.symm (clamp01 r) = p (clamp01 (1 - r)) := by
  rw [path_symm_apply, symm_clamp01]

theorem sigma_zero (t : M → I) : sigma 0 t = t := by
  funext j
  apply Subtype.ext
  rw [sigma_apply, coe_scale]
  rw [show ((t j : I) : ℝ) - 0 = (t j : ℝ) by ring,
    show (1 : ℝ) - 2 * 0 = 1 by norm_num, div_one]
  rw [min_eq_right (t j).2.2, max_eq_right (t j).2.1]

/-! ## The continuous "warp" `(s,t) ↦ sigma ((1-s)/4) t` and its square -/

omit [Fintype M] [Nonempty M] in
theorem continuous_sigmaW : Continuous fun q : I × (M → I) =>
    sigma ((1 - (q.1 : ℝ)) / 4) q.2 := by
  refine continuous_pi (fun j => ?_)
  have hW : Continuous (fun q : I × (M → I) =>
      (((q.2 j : I) : ℝ) - (1 - (q.1 : ℝ)) / 4) /
        (1 - 2 * ((1 - (q.1 : ℝ)) / 4))) := by
    refine Continuous.div ?_ ?_ ?_
    · exact (continuous_subtype_val.comp ((continuous_apply j).comp continuous_snd)).sub
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).div_const 4)
    · exact continuous_const.sub (continuous_const.mul
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).div_const 4))
    · intro q
      have hq : (0 : ℝ) ≤ (q.1 : ℝ) := q.1.2.1
      have hden : (1 : ℝ) - 2 * ((1 - (q.1 : ℝ)) / 4) = (1 + (q.1 : ℝ)) / 2 := by ring
      rw [hden]
      linarith
  exact continuous_clamp01.comp hW

noncomputable def sigmaW : C(I × (M → I), M → I) where
  toFun q := sigma ((1 - (q.1 : ℝ)) / 4) q.2
  continuous_toFun := continuous_sigmaW

noncomputable def sigmaWsq : C(I × (M → I), M → I) :=
  sigmaW.comp ⟨fun q : I × (M → I) => (q.1, sigmaW q),
    continuous_fst.prodMk sigmaW.continuous⟩

@[simp] theorem sigmaW_apply (s : I) (t : M → I) :
    sigmaW (s, t) = sigma ((1 - (s : ℝ)) / 4) t := rfl

@[simp] theorem sigmaWsq_apply (s : I) (t : M → I) :
    sigmaWsq (s, t) = sigma ((1 - (s : ℝ)) / 4) (sigma ((1 - (s : ℝ)) / 4) t) := rfl

/-! ## The two intermediate maps `A` and `B` -/

theorem continuous_Bfun : Continuous fun z : (Ω^ M X x) × (M → I) =>
    z.1 (sigma (1 / 4) (sigma (1 / 4) z.2)) :=
  Continuous.eval continuous_fst
    ((continuous_sigma (1 / 4)).comp ((continuous_sigma (1 / 4)).comp continuous_snd))

/-- The self-map `B` of the loop space given by precomposition with `sigma 1/4 ∘ sigma 1/4`. -/
noncomputable def B : C(Ω^ M X x, Ω^ M X x) where
  toFun f :=
    ⟨⟨fun t => f (sigma (1 / 4) (sigma (1 / 4) t)),
      continuous_Bfun.comp (show Continuous fun t : (M → I) => (f, t) from
        continuous_const.prodMk continuous_id)⟩,
      fun _ ht => GenLoop.boundary f _
        (sigma_quarter_mem_boundary (sigma_quarter_mem_boundary ht))⟩
  continuous_toFun := Continuous.subtype_mk
    (ContinuousMap.continuous_of_continuous_uncurry
      (fun f => ⟨fun t => f (sigma (1 / 4) (sigma (1 / 4) t)),
        continuous_Bfun.comp (show Continuous fun t : (M → I) => (f, t) from
          continuous_const.prodMk continuous_id)⟩) continuous_Bfun)
    (fun f => fun _ ht => GenLoop.boundary f _
      (sigma_quarter_mem_boundary (sigma_quarter_mem_boundary ht)))

@[simp] theorem B_apply (f : Ω^ M X x) (t : M → I) :
    B f t = f (sigma (1 / 4) (sigma (1 / 4) t)) := rfl

theorem continuous_Afun : Continuous fun z : (Ω^ M X x) × (M → I) =>
    (if delta z.2 ≤ 3 / 8 then x else z.1 (sigma (1 / 4) (sigma (1 / 4) z.2))) := by
  have hd : Continuous fun z : (Ω^ M X x) × (M → I) => delta z.2 :=
    continuous_delta.comp continuous_snd
  refine Continuous.if_le continuous_const continuous_Bfun hd continuous_const ?_
  intro z hz
  have hb : sigma (1 / 4) (sigma (1 / 4) z.2) ∈ Cube.boundary M :=
    sigma_sigma_mem_boundary_of_delta_le (le_of_eq hz)
  exact (GenLoop.boundary _ _ hb).symm

/-- The loop vanishing on the collar `{delta ≤ 3/8}` and equal to the doubly shrunk loop inside. -/
noncomputable def A : C(Ω^ M X x, Ω^ M X x) where
  toFun f :=
    ⟨⟨fun t => if delta t ≤ 3 / 8 then x else f (sigma (1 / 4) (sigma (1 / 4) t)),
      continuous_Afun.comp (show Continuous fun t : (M → I) => (f, t) from
        continuous_const.prodMk continuous_id)⟩,
      fun t ht => by
        show (if delta t ≤ 3 / 8 then x else f (sigma (1 / 4) (sigma (1 / 4) t))) = x
        exact if_pos (show delta t ≤ 3 / 8 from by
          rw [(delta_eq_zero_iff).mpr ht]; norm_num)⟩
  continuous_toFun := Continuous.subtype_mk
    (ContinuousMap.continuous_of_continuous_uncurry
      (fun f => ⟨fun t => if delta t ≤ 3 / 8 then x else f (sigma (1 / 4) (sigma (1 / 4) t)),
        continuous_Afun.comp (show Continuous fun t : (M → I) => (f, t) from
          continuous_const.prodMk continuous_id)⟩) continuous_Afun)
    (fun f => fun t ht => by
      show (if delta t ≤ 3 / 8 then x else f (sigma (1 / 4) (sigma (1 / 4) t))) = x
      exact if_pos (show delta t ≤ 3 / 8 from by
        rw [(delta_eq_zero_iff).mpr ht]; norm_num))

@[simp] theorem A_apply (f : Ω^ M X x) (t : M → I) :
    A f t = (if delta t ≤ 3 / 8 then x else f (sigma (1 / 4) (sigma (1 / 4) t))) := rfl

/-! ## The first homotopy: contracting the path part -/

/-- The composite `collar p.symm ∘ collar p`. -/
noncomputable def Phi (p : Path x y) : C(Ω^ M X x, Ω^ M X x) :=
  (collar p.symm).comp (collar p)

theorem Phi_apply (p : Path x y) (f : Ω^ M X x) (t : M → I) :
    Phi p f t = (if delta t ≤ 1 / 4 then p (clamp01 (4 * delta t))
      else if delta (sigma (1 / 4) t) ≤ 1 / 4 then p (clamp01 (1 - 4 * delta (sigma (1 / 4) t)))
      else f (sigma (1 / 4) (sigma (1 / 4) t))) := by
  rw [Phi, ContinuousMap.comp_apply, collar_apply, collarFun]
  by_cases h : delta t ≤ 1 / 4
  · simp only [if_pos h]
    rw [path_symm_clamp01 p (1 - 4 * delta t)]
    rw [show (1 : ℝ) - (1 - 4 * delta t) = 4 * delta t by ring]
  · simp only [if_neg h]
    rw [collar_apply, collarFun]

/-- The pointwise formula of the first homotopy: the two path branches are multiplied by the
homotopy parameter inside `clamp01`. -/
noncomputable def H1fun (p : Path x y) (q : I × (Ω^ M X x)) (t : M → I) : X :=
  if delta t ≤ 1 / 4 then p (clamp01 ((q.1 : ℝ) * (4 * delta t)))
  else if delta (sigma (1 / 4) t) ≤ 1 / 4 then
    p (clamp01 ((q.1 : ℝ) * (1 - 4 * delta (sigma (1 / 4) t))))
  else q.2 (sigma (1 / 4) (sigma (1 / 4) t))

theorem continuous_H1fun (p : Path x y) :
    Continuous (fun z : (I × (Ω^ M X x)) × (M → I) => H1fun p z.1 z.2) := by
  have hd : Continuous fun z : (I × (Ω^ M X x)) × (M → I) => delta z.2 :=
    continuous_delta.comp continuous_snd
  have hs : Continuous fun z : (I × (Ω^ M X x)) × (M → I) => (z.1.1 : ℝ) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  have hA1 : Continuous fun z : (I × (Ω^ M X x)) × (M → I) =>
      p (clamp01 ((z.1.1 : ℝ) * (4 * delta z.2))) :=
    p.continuous.comp (continuous_clamp01.comp (hs.mul (continuous_const.mul hd)))
  have hd2 : Continuous fun z : (I × (Ω^ M X x)) × (M → I) =>
      delta (sigma (1 / 4) z.2) :=
    continuous_delta.comp ((continuous_sigma (1 / 4)).comp continuous_snd)
  have hB1 : Continuous fun z : (I × (Ω^ M X x)) × (M → I) =>
      p (clamp01 ((z.1.1 : ℝ) * (1 - 4 * delta (sigma (1 / 4) z.2)))) :=
    p.continuous.comp (continuous_clamp01.comp
      (hs.mul (continuous_const.sub (continuous_const.mul hd2))))
  have hC1 : Continuous fun z : (I × (Ω^ M X x)) × (M → I) =>
      z.1.2 (sigma (1 / 4) (sigma (1 / 4) z.2)) :=
    Continuous.eval (continuous_snd.comp continuous_fst)
      ((continuous_sigma (1 / 4)).comp ((continuous_sigma (1 / 4)).comp continuous_snd))
  have hinner : Continuous fun z : (I × (Ω^ M X x)) × (M → I) =>
      if delta (sigma (1 / 4) z.2) ≤ 1 / 4
        then p (clamp01 ((z.1.1 : ℝ) * (1 - 4 * delta (sigma (1 / 4) z.2))))
        else z.1.2 (sigma (1 / 4) (sigma (1 / 4) z.2)) := by
    refine Continuous.if_le hB1 hC1 hd2 continuous_const ?_
    intro z hz
    have hb : sigma (1 / 4) (sigma (1 / 4) z.2) ∈ Cube.boundary M :=
      sigma_mem_boundary_of_delta_le (by norm_num) (le_of_eq hz)
    have harg : (z.1.1 : ℝ) * (1 - 4 * delta (sigma (1 / 4) z.2)) = 0 := by
      rw [hz]; ring
    rw [harg, clamp01_zero, p.source]
    exact (GenLoop.boundary _ _ hb).symm
  refine Continuous.if_le hA1 hinner hd continuous_const ?_
  intro z hz
  have h0 : delta (sigma (1 / 4) z.2) = 0 :=
    delta_sigma_eq_zero_of_delta_le_quarter (le_of_eq hz)
  rw [if_pos (by rw [h0]; norm_num)]
  have harg1 : (z.1.1 : ℝ) * (4 * delta z.2) = (z.1.1 : ℝ) := by rw [hz]; ring
  have harg2 : (z.1.1 : ℝ) * (1 - 4 * delta (sigma (1 / 4) z.2)) = (z.1.1 : ℝ) := by
    rw [h0]; ring
  rw [harg1, harg2, clamp01_coe]

theorem H1fun_boundary (p : Path x y) (q : I × (Ω^ M X x)) {t : M → I}
    (ht : t ∈ Cube.boundary M) : H1fun p q t = x := by
  have h0 : delta t = 0 := (delta_eq_zero_iff).mpr ht
  rw [H1fun, if_pos (show delta t ≤ 1 / 4 by rw [h0]; norm_num)]
  have harg : (q.1 : ℝ) * (4 * delta t) = 0 := by rw [h0]; ring
  rw [harg, clamp01_zero]
  exact p.source

noncomputable def H1 (p : Path x y) : C(I × (Ω^ M X x), Ω^ M X x) where
  toFun q :=
    ⟨⟨fun t => H1fun p q t,
      (continuous_H1fun p).comp (show Continuous fun t : (M → I) => (q, t) from
        continuous_const.prodMk continuous_id)⟩,
      fun _ ht => H1fun_boundary p q ht⟩
  continuous_toFun := Continuous.subtype_mk
    (ContinuousMap.continuous_of_continuous_uncurry
      (fun q => ⟨fun t => H1fun p q t,
        (continuous_H1fun p).comp (show Continuous fun t : (M → I) => (q, t) from
          continuous_const.prodMk continuous_id)⟩) (continuous_H1fun p))
    (fun q => fun _ ht => H1fun_boundary p q ht)

@[simp] theorem H1_apply (p : Path x y) (q : I × (Ω^ M X x)) (t : M → I) :
    H1 p q t = H1fun p q t := rfl

theorem H1_zero (p : Path x y) (f : Ω^ M X x) : H1 p (0, f) = A f := by
  apply GenLoop.ext
  intro t
  rw [H1_apply]
  simp only [H1fun, A_apply]
  rw [show ((0 : I) : ℝ) = 0 from rfl]
  by_cases h : delta t ≤ 1 / 4
  · have h38 : delta t ≤ 3 / 8 := by linarith
    simp only [if_pos h, if_pos h38]
    rw [show (0 : ℝ) * (4 * delta t) = 0 by ring, clamp01_zero, p.source]
  · simp only [if_neg h]
    by_cases h2 : delta (sigma (1 / 4) t) ≤ 1 / 4
    · have h3 : delta t ≤ 3 / 8 := (delta_sigma_quarter_iff t).mp h2
      simp only [if_pos h2, if_pos h3]
      rw [show (0 : ℝ) * (1 - 4 * delta (sigma (1 / 4) t)) = 0 by ring, clamp01_zero, p.source]
    · have h3 : ¬ delta t ≤ 3 / 8 := fun hh => h2 ((delta_sigma_quarter_iff t).mpr hh)
      simp only [if_neg h2, if_neg h3]

theorem H1_one (p : Path x y) (f : Ω^ M X x) : H1 p (1, f) = Phi p f := by
  apply GenLoop.ext
  intro t
  rw [H1_apply, Phi_apply]
  simp only [H1fun]
  rw [show ((1 : I) : ℝ) = 1 from rfl]
  by_cases h : delta t ≤ 1 / 4
  · simp only [if_pos h, one_mul]
  · simp only [if_neg h]
    by_cases h2 : delta (sigma (1 / 4) t) ≤ 1 / 4
    · simp only [if_pos h2, one_mul]
    · simp only [if_neg h2]

noncomputable def hom1 (p : Path x y) :
    ContinuousMap.Homotopy (A : C(Ω^ M X x, Ω^ M X x)) (Phi p) :=
  ContinuousMap.Homotopy.mk (H1 p) (fun f => H1_zero p f) (fun f => H1_one p f)

/-! ## The second homotopy: shrinking the constant collar to nothing -/

noncomputable def H2fun (q : I × (Ω^ M X x)) (t : M → I) : X :=
  if delta t ≤ (1 - (q.1 : ℝ)) * (3 / 8) then x else q.2 (sigma (1 / 4) (sigma (1 / 4) t))

theorem continuous_H2fun :
    Continuous (fun z : (I × (Ω^ M X x)) × (M → I) => H2fun z.1 z.2) := by
  have hd : Continuous fun z : (I × (Ω^ M X x)) × (M → I) => delta z.2 :=
    continuous_delta.comp continuous_snd
  have hg : Continuous fun z : (I × (Ω^ M X x)) × (M → I) =>
      (1 - (z.1.1 : ℝ)) * (3 / 8) :=
    (continuous_const.sub (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))).mul
      continuous_const
  have hC : Continuous fun z : (I × (Ω^ M X x)) × (M → I) =>
      z.1.2 (sigma (1 / 4) (sigma (1 / 4) z.2)) :=
    Continuous.eval (continuous_snd.comp continuous_fst)
      ((continuous_sigma (1 / 4)).comp ((continuous_sigma (1 / 4)).comp continuous_snd))
  refine Continuous.if_le continuous_const hC hd hg ?_
  intro z hz
  have hle : delta z.2 ≤ 3 / 8 := by
    rw [hz]
    have h1 : (0 : ℝ) ≤ (z.1.1 : ℝ) := z.1.1.2.1
    nlinarith [z.1.1.2.2]
  have hb : sigma (1 / 4) (sigma (1 / 4) z.2) ∈ Cube.boundary M :=
    sigma_sigma_mem_boundary_of_delta_le hle
  exact (GenLoop.boundary _ _ hb).symm

noncomputable def H2 : C(I × (Ω^ M X x), Ω^ M X x) where
  toFun q :=
    ⟨⟨fun t => H2fun q t,
      continuous_H2fun.comp (show Continuous fun t : (M → I) => (q, t) from
        continuous_const.prodMk continuous_id)⟩,
      fun t ht => by
        have h0 : delta t = 0 := (delta_eq_zero_iff).mpr ht
        have hle : delta t ≤ (1 - (q.1 : ℝ)) * (3 / 8) := by
          rw [h0]
          have h1 : (0 : ℝ) ≤ 1 - (q.1 : ℝ) := by linarith [q.1.2.2]
          nlinarith
        show H2fun q t = x
        simp only [H2fun, if_pos hle]⟩
  continuous_toFun := Continuous.subtype_mk
    (ContinuousMap.continuous_of_continuous_uncurry
      (fun q => ⟨fun t => H2fun q t,
        continuous_H2fun.comp (show Continuous fun t : (M → I) => (q, t) from
          continuous_const.prodMk continuous_id)⟩) continuous_H2fun)
    (fun q => fun t ht => by
      have h0 : delta t = 0 := (delta_eq_zero_iff).mpr ht
      have hle : delta t ≤ (1 - (q.1 : ℝ)) * (3 / 8) := by
        rw [h0]
        have h1 : (0 : ℝ) ≤ 1 - (q.1 : ℝ) := by linarith [q.1.2.2]
        nlinarith
      show H2fun q t = x
      simp only [H2fun, if_pos hle])

@[simp] theorem H2_apply (q : I × (Ω^ M X x)) (t : M → I) :
    H2 q t = H2fun q t := rfl

theorem H2_zero (f : Ω^ M X x) : H2 (0, f) = A f := by
  apply GenLoop.ext
  intro t
  rw [H2_apply, H2fun, A_apply]
  have h0 : (1 : ℝ) - ((0 : I) : ℝ) = 1 := by norm_num
  rw [h0, one_mul]

theorem H2_one (f : Ω^ M X x) : H2 (1, f) = B f := by
  apply GenLoop.ext
  intro t
  rw [H2_apply, H2fun, B_apply]
  have h0 : (1 : ℝ) - ((1 : I) : ℝ) = 0 := by norm_num
  rw [h0, zero_mul]
  by_cases h : delta t ≤ 0
  · have hz : delta t = 0 := le_antisymm h (delta_nonneg t)
    have ht : t ∈ Cube.boundary M := (delta_eq_zero_iff).mp hz
    simp only [if_pos h]
    exact (GenLoop.boundary f _
      (sigma_quarter_mem_boundary (sigma_quarter_mem_boundary ht))).symm
  · simp only [if_neg h]

noncomputable def hom2 : ContinuousMap.Homotopy (A : C(Ω^ M X x, Ω^ M X x)) B :=
  ContinuousMap.Homotopy.mk H2 H2_zero H2_one

/-! ## The third homotopy: un-shrinking the cube -/

noncomputable def H3fun (q : I × (Ω^ M X x)) (t : M → I) : X := q.2 (sigmaWsq (q.1, t))

theorem continuous_H3fun :
    Continuous (fun z : (I × (Ω^ M X x)) × (M → I) => H3fun z.1 z.2) :=
  Continuous.eval (continuous_snd.comp continuous_fst)
    (sigmaWsq.continuous.comp
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd))

theorem H3fun_boundary (q : I × (Ω^ M X x)) {t : M → I} (ht : t ∈ Cube.boundary M) :
    H3fun q t = x := by
  have hs0 : (0 : ℝ) ≤ (q.1 : ℝ) := q.1.2.1
  have hs1 : (q.1 : ℝ) ≤ 1 := q.1.2.2
  have hw0 : (0 : ℝ) ≤ (1 - (q.1 : ℝ)) / 4 := by linarith
  have hw1 : (1 - (q.1 : ℝ)) / 4 < 1 / 2 := by linarith
  have hb : sigma ((1 - (q.1 : ℝ)) / 4) (sigma ((1 - (q.1 : ℝ)) / 4) t) ∈ Cube.boundary M :=
    sigma_mem_boundary hw0 hw1 (sigma_mem_boundary hw0 hw1 ht)
  rw [H3fun, sigmaWsq_apply]
  exact GenLoop.boundary q.2 _ hb

noncomputable def H3 : C(I × (Ω^ M X x), Ω^ M X x) where
  toFun q :=
    ⟨⟨fun t => H3fun q t,
      continuous_H3fun.comp (show Continuous fun t : (M → I) => (q, t) from
        continuous_const.prodMk continuous_id)⟩,
      fun _ ht => H3fun_boundary q ht⟩
  continuous_toFun := Continuous.subtype_mk
    (ContinuousMap.continuous_of_continuous_uncurry
      (fun q => ⟨fun t => H3fun q t,
        continuous_H3fun.comp (show Continuous fun t : (M → I) => (q, t) from
          continuous_const.prodMk continuous_id)⟩) continuous_H3fun)
    (fun q => fun _ ht => H3fun_boundary q ht)

@[simp] theorem H3_apply (q : I × (Ω^ M X x)) (t : M → I) :
    H3 q t = H3fun q t := rfl

theorem H3_zero (f : Ω^ M X x) : H3 (0, f) = B f := by
  apply GenLoop.ext
  intro t
  rw [H3_apply, H3fun, sigmaWsq_apply, B_apply]
  have h0 : (1 : ℝ) - ((0 : I) : ℝ) = 1 := by norm_num
  rw [h0]

theorem H3_one (f : Ω^ M X x) : H3 (1, f) = ContinuousMap.id (Ω^ M X x) f := by
  apply GenLoop.ext
  intro t
  rw [H3_apply, H3fun, sigmaWsq_apply, ContinuousMap.id_apply]
  have h0 : (1 : ℝ) - ((1 : I) : ℝ) = 0 := by norm_num
  rw [h0]
  norm_num
  rw [sigma_zero, sigma_zero]

noncomputable def hom3 :
    ContinuousMap.Homotopy (B : C(Ω^ M X x, Ω^ M X x)) (ContinuousMap.id (Ω^ M X x)) :=
  ContinuousMap.Homotopy.mk H3 H3_zero H3_one

/-! ## The collapse -/

theorem collar_collapse {M : Type*} [Fintype M] [Nonempty M] {X : Type*} [TopologicalSpace X]
    {x y : X} (p : Path x y) :
    Nonempty (ContinuousMap.Homotopy
      ((Work.Stems.Collar.collar p.symm).comp (Work.Stems.Collar.collar p))
      (ContinuousMap.id (GenLoop M X x))) :=
  ⟨(hom1 p).symm.trans (hom2.trans hom3)⟩

end Work.Stems.Collar
