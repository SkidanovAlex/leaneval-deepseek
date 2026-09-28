import Mathlib
import Submission.Work.HP.Q44Child.SuperDefs
import Submission.Work.HP.Q44Child.SuperAux
import Submission.Work.HP.Q44Child.superlattice_basis
import Submission.Work.HP.Q44Child.real_span_inter
import Submission.Work.HP.Q44Child.linIndep_triple_of_notMem
import Submission.Work.HP.Q44Child.SuperCount

/-!
# The injection of superlattices into `Γ Λ`

Every rank-`3` superlattice `L ⊇ Λ` with `detL L ≤ T * detL Λ` is mapped to the generator
`u ∈ Γ Λ` of the rank-`1` subgroup `π(L) ≤ Γ Λ`, whose norm is `detL L / detL Λ ≤ T`.
The map is injective, because `L` is recovered from `u` as
`{w : ℤ^5 | π (toE w) ∈ ℤ • u}` (using primitivity of `Λ`).
-/

namespace Work.HP.Q44Child

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option linter.deprecated false

noncomputable section

open scoped RealInnerProductSpace
open Module

variable {Λ : Submodule ℤ (Fin 5 → ℤ)}
variable {b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)}

lemma hcast_inj' : Function.Injective fun r : ℤ => r • (1 : ℝ) := by
  intro a c hac
  exact Int.cast_injective (α := ℝ) (by simpa using hac)

lemma pair_zero (b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)) :
    pair b 0 = b (Fin.castLE (by norm_num : 2 ≤ 5) 0) := rfl

lemma pair_one (b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)) :
    pair b 1 = b (Fin.castLE (by norm_num : 2 ≤ 5) 1) := rfl

lemma span_pair_eq (b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)) :
    Submodule.span ℤ (Set.range (pair b))
      = Submodule.span ℤ (Set.range fun i : Fin 2 => b (Fin.castLE (by norm_num : 2 ≤ 5) i)) :=
  rfl

lemma triple_set_eq (b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)) (v : Fin 5 → ℤ) :
    ({pair b 0, pair b 1, v} : Set (Fin 5 → ℤ))
      = {b (Fin.castLE (by norm_num : 2 ≤ 5) 0),
          b (Fin.castLE (by norm_num : 2 ≤ 5) 1), v} := by
  rw [pair_zero, pair_one]

lemma finSum21_inl (a : Fin 2) :
    finSumFinEquiv (m := 2) (n := 1) (Sum.inl a) = (Fin.castAdd 1 a : Fin 3) :=
  finSumFinEquiv_apply_left a

lemma finSum21_inr (c : Fin 1) :
    finSumFinEquiv (m := 2) (n := 1) (Sum.inr c) = (Fin.natAdd 2 c : Fin 3) :=
  finSumFinEquiv_apply_right c

/-- The set `{b 0, b 1, v}` as the range of a `Sum (Fin 2) (Fin 1)`-indexed family. -/
lemma range_sum_elim (v : Fin 5 → ℤ) :
    Set.range (Sum.elim (fun i : Fin 2 => pair b i) (fun _ : Fin 1 => v))
      = ({pair b 0, pair b 1, v} : Set (Fin 5 → ℤ)) := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    cases i with
    | inl a => fin_cases a <;> simp
    | inr c => fin_cases c <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨Sum.inl 0, by simp⟩
    · exact ⟨Sum.inl 1, by simp⟩
    · exact ⟨Sum.inr 0, by simp⟩

/-- Membership in `ΓW Λ` of `π (toE v)`. -/
lemma proj_toE_mem_ΓW (v : Fin 5 → ℤ) : (⟨proj Λ (toE v), proj_mem Λ _⟩ : W Λ) ∈ ΓW Λ := by
  have := Ψ_mem_ΓW (Λ := Λ) v
  simpa [Ψ_apply] using this

section Triple

variable {Λ : Submodule ℤ (Fin 5 → ℤ)}
variable {b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)}

/-- The `Sum (Fin 2) (Fin 1)`-indexed family `b 0, b 1, v`. -/
def tripS (b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)) (v : Fin 5 → ℤ) :
    Sum (Fin 2) (Fin 1) → (Fin 5 → ℤ) :=
  Sum.elim (fun i : Fin 2 => pair b i) (fun _ : Fin 1 => v)

/-- `ℝ`-independence of the triple `toE (b 0), toE (b 1), toE v`, `Sum`-indexed. -/
lemma linIndep_tripS (hb : Λ = Submodule.span ℤ (Set.range (pair b)))
    {v : Fin 5 → ℤ} (hv : v ∉ Submodule.span ℤ (Set.range (pair b))) :
    LinearIndependent ℝ (fun i : Sum (Fin 2) (Fin 1) => toE (tripS b v i)) := by
  have hv' : v ∉ Submodule.span ℤ (Set.range fun i : Fin 2 =>
      b (Fin.castLE (by norm_num : 2 ≤ 5) i)) := by
    rwa [show (fun i : Fin 2 => b (Fin.castLE (by norm_num : 2 ≤ 5) i)) = pair b from rfl]
  have htriple : LinearIndependent ℝ ![toE (pair b 0), toE (pair b 1), toE v] :=
    linIndep_triple_of_notMem (b := b) (v := v) hv'
  have h := htriple.comp (finSumFinEquiv (m := 2) (n := 1)) (Equiv.injective _)
  convert h using 1
  funext i
  cases i with
  | inl a => fin_cases a <;> simp [tripS, finSum21_inl, Fin.castAdd, Fin.castLE,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  | inr c => fin_cases c <;> simp [tripS, finSum21_inr, Fin.natAdd, Matrix.cons_val_two,
      Matrix.head_cons]

/-- `detL` of `L = span {b 0, b 1, v}` in terms of `v`. -/
lemma detL_triple (hb : Λ = Submodule.span ℤ (Set.range (pair b)))
    (hli : LinearIndependent ℝ (fun i : Fin 5 => toE (b i)))
    {v : Fin 5 → ℤ} (hv : v ∉ Submodule.span ℤ (Set.range (pair b)))
    {L : Submodule ℤ (Fin 5 → ℤ)}
    (hLspan : L = Submodule.span ℤ ({pair b 0, pair b 1, v} : Set (Fin 5 → ℤ))) :
    detL L = detL Λ * ‖proj Λ (toE v)‖ := by
  have hindep := linIndep_tripS (b := b) hb hv
  -- ℤ-generators of `L`, indexed by `Sum (Fin 2) (Fin 1)`
  have hspan3 : Submodule.span ℤ (Set.range (tripS b v)) = L := by
    rw [hLspan, show Set.range (tripS b v) = ({pair b 0, pair b 1, v} : Set (Fin 5 → ℤ))
      from range_sum_elim v]
  let w : Sum (Fin 2) (Fin 1) → L := fun i => ⟨tripS b v i, by
    rw [← hspan3]; exact Submodule.subset_span ⟨i, rfl⟩⟩
  have hw_apply : ∀ i, ((w i : L) : Fin 5 → ℤ) = tripS b v i := fun i => rfl
  have hLI_Z : LinearIndependent ℤ w := by
    refine LinearIndependent.of_comp (Submodule.subtype L) ?_
    refine LinearIndependent.of_comp toE ?_
    refine LinearIndependent.restrict_scalars (R := ℤ) hcast_inj' ?_
    simpa only [Function.comp_def, Submodule.coe_subtype, Subtype.coe_mk] using hindep
  let bL : Basis (Sum (Fin 2) (Fin 1)) ℤ L := Basis.mk (v := w) hLI_Z
    (by
      intro x _
      have hx : (x : Fin 5 → ℤ) ∈ Submodule.span ℤ (Set.range (tripS b v)) := by
        rw [hspan3]
        exact x.2
      refine Submodule.span_induction (p := fun y hy => (⟨y, by rw [← hspan3]; exact hy⟩ : L) ∈
          Submodule.span ℤ (Set.range w)) ?_ ?_ ?_ ?_ hx
      · rintro y ⟨i, rfl⟩
        exact Submodule.subset_span ⟨i, rfl⟩
      · exact Submodule.zero_mem _
      · intro y z hy hz hhy hhz
        exact Submodule.add_mem _ hhy hhz
      · intro c y hy hhy
        exact Submodule.smul_mem _ c hhy)
  have hbL_apply : ∀ i, ((bL i : L) : Fin 5 → ℤ) = tripS b v i := by
    intro i
    exact congrArg Subtype.val (Module.Basis.mk_apply (v := w) _ _ i)
  have hgram : (Matrix.of fun i j : Sum (Fin 2) (Fin 1) =>
        ∑ x, ((((bL i : L) : Fin 5 → ℤ) x : ℝ) * (((bL j : L) : Fin 5 → ℤ) x : ℝ)))
      = Matrix.gram ℝ (fun i : Sum (Fin 2) (Fin 1) =>
          Sum.elim (fun i : Fin 2 => toE (pair b i)) (fun _ : Fin 1 => toE v) i) := by
    ext i j
    cases i <;> cases j <;>
      simp only [tripS, Sum.elim_inl, Sum.elim_inr, Matrix.of_apply, Matrix.gram_apply,
        hbL_apply, inner_toE]

  have hdetL : detL L = Real.sqrt ((Matrix.gram ℝ (fun i : Sum (Fin 2) (Fin 1) =>
        Sum.elim (fun i : Fin 2 => toE (pair b i)) (fun _ : Fin 1 => toE v) i)).det) := by
    rw [Work.HP.Lat.detL_basis_gram L bL, hgram]
  -- the projected Gram determinant
  have hW : (Submodule.span ℝ (Set.range fun i : Fin 2 => toE (pair b i)))ᗮ = W Λ := by
    rw [W, ← Lℝ_eq_of_basis hb]
  have hproj : (fun _ : Fin 1 => (Submodule.span ℝ
        (Set.range fun i : Fin 2 => toE (pair b i)))ᗮ.starProjection (toE v))
      = fun _ : Fin 1 => proj Λ (toE v) := by
    funext j
    refine Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_
    · rw [hW, proj]
      exact Submodule.starProjection_apply_mem (W Λ) _
    · rw [hW, proj]
      exact Submodule.sub_starProjection_mem_orthogonal _
  have hgp := gram_proj_det' (E := E5) (fun i : Fin 2 => toE (pair b i))
    (fun _ : Fin 1 => toE v) (pair_linIndep hli)
  rw [hproj] at hgp
  rw [det_gram_pair_eq hb hli] at hgp
  have hone : (Matrix.gram ℝ (fun _ : Fin 1 => proj Λ (toE v))).det = ‖proj Λ (toE v)‖ ^ 2 := by
    rw [Matrix.det_fin_one, Matrix.gram_apply, real_inner_self_eq_norm_sq]
  rw [hone] at hgp
  rw [hdetL, hgp, ← mul_pow, Real.sqrt_sq
    (mul_nonneg (le_of_lt (detL_pos hb hli)) (norm_nonneg _))]

end Triple

section ExistsGen

variable {Λ : Submodule ℤ (Fin 5 → ℤ)}
variable {b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)}

/-- Membership in `Submodule.span ℤ {x}`. -/
lemma mem_span_singleton_iff {x y : Fin 5 → ℤ} :
    y ∈ Submodule.span ℤ ({x} : Set (Fin 5 → ℤ)) ↔ ∃ m : ℤ, m • x = y :=
  Submodule.mem_span_singleton

/-- For `L ∈ Sset Λ T` there is a generator `u ∈ Γ Λ` of the rank-`1` group `π(L)` with
`‖u‖ ≤ T`, and `L` is recovered from `u`. -/
lemma exists_gen (hb : Λ = Submodule.span ℤ (Set.range (pair b)))
    (hli : LinearIndependent ℝ (fun i : Fin 5 => toE (b i)))
    (h5 : (Matrix.gram ℝ (fun i : Fin 5 => toE (b i))).det = 1)
    (hΛrk : rk Λ = 2) (hpr : IsPrimLat Λ) {T : ℝ}
    {L : Submodule ℤ (Fin 5 → ℤ)} (hL : L ∈ Sset Λ T) :
    ∃ u : W Λ, u ∈ ΓW Λ ∧ ‖(u : E5)‖ ≤ T ∧
      ∀ w : Fin 5 → ℤ, w ∈ L ↔ ∃ m : ℤ, proj Λ (toE w) = m • (u : E5) := by
  obtain ⟨hLle, hLrk, hLdet⟩ := hL
  obtain ⟨v, hvL, hLspan₀⟩ := superlattice_basis b L (by rw [← span_pair_eq b, ← hb]; exact hLle) hLrk
  have hLspan : L = Submodule.span ℤ ({pair b 0, pair b 1, v} : Set (Fin 5 → ℤ)) := by
    rw [hLspan₀, triple_set_eq b v]
  -- `v ∉ Λ`
  have hv_notin : v ∉ Submodule.span ℤ (Set.range (pair b)) := by
    intro hv
    have hspan_le : Submodule.span ℤ ({pair b 0, pair b 1, v} : Set (Fin 5 → ℤ))
        ≤ Submodule.span ℤ (Set.range (pair b)) := by
      rw [Submodule.span_le]
      rintro x (rfl | rfl | rfl)
      · exact Submodule.subset_span ⟨0, rfl⟩
      · exact Submodule.subset_span ⟨1, rfl⟩
      · exact hv
    have hspan_ge : Submodule.span ℤ (Set.range (pair b))
        ≤ Submodule.span ℤ ({pair b 0, pair b 1, v} : Set (Fin 5 → ℤ)) := by
      rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      fin_cases i
      · exact Submodule.subset_span (by simp)
      · exact Submodule.subset_span (by simp)
    rw [hLspan] at hLrk
    rw [show Submodule.span ℤ ({pair b 0, pair b 1, v} : Set (Fin 5 → ℤ))
        = Submodule.span ℤ (Set.range (pair b)) from le_antisymm hspan_le hspan_ge, ← hb] at hLrk
    omega
  -- the determinant identity and the norm bound
  have hdetL := detL_triple (b := b) hb hli hv_notin hLspan
  have hnorm : ‖proj Λ (toE v)‖ ≤ T := by
    have hpos := detL_pos hb hli
    have h2 : detL Λ * ‖proj Λ (toE v)‖ ≤ detL Λ * T := by
      rw [← hdetL, mul_comm (detL Λ) T]
      exact hLdet
    exact le_of_mul_le_mul_left h2 hpos
  -- the reconstruction of `L` from `π (toE v)`
  have hrecon : ∀ w : Fin 5 → ℤ,
      w ∈ L ↔ ∃ m : ℤ, proj Λ (toE w) = m • proj Λ (toE v) := by
    intro w
    constructor
    · intro hw
      rw [hLspan] at hw
      have hmem : proj Λ (toE w) ∈ Submodule.span ℤ ({proj Λ (toE v)} : Set E5) := by
        refine Submodule.span_induction (p := fun y _ =>
          proj Λ (toE y) ∈ Submodule.span ℤ ({proj Λ (toE v)} : Set E5)) ?_ ?_ ?_ ?_ hw
        · rintro y (rfl | rfl | rfl)
          · rw [proj_kills_toE Λ (v := pair b 0)
              (by rw [hb]; exact Submodule.subset_span ⟨0, rfl⟩)]
            exact Submodule.zero_mem _
          · rw [proj_kills_toE Λ (v := pair b 1)
              (by rw [hb]; exact Submodule.subset_span ⟨1, rfl⟩)]
            exact Submodule.zero_mem _
          · exact Submodule.subset_span (by simp)
        · simp
        · intro y z _ _ hy hz
          rw [toE_add, map_add]
          exact Submodule.add_mem _ hy hz
        · intro c y _ hy
          rw [toE_smul, map_zsmul]
          exact Submodule.smul_mem (Submodule.span ℤ ({proj Λ (toE v)} : Set E5)) c hy
      obtain ⟨m, hm⟩ := (Submodule.mem_span_singleton (R := ℤ) (y := proj Λ (toE v))).mp hmem
      exact ⟨m, hm.symm⟩
    · rintro ⟨m, hm⟩
      have hzero : proj Λ (toE (w - m • v)) = 0 := by
        rw [toE_sub, toE_smul, map_sub, map_zsmul, hm]
        simp
      have hmemℝ : toE (w - m • v) ∈ Lℝ Λ := (proj_eq_zero_iff Λ _).mp hzero
      have hmemΛ : w - m • v ∈ Λ := real_span_inter Λ hpr (w - m • v) hmemℝ
      have h1 : w - m • v ∈ L := hLle hmemΛ
      have h2 : m • v ∈ L := Submodule.smul_mem _ _ hvL
      have := Submodule.add_mem _ h1 h2
      simpa [sub_add_cancel] using this
  exact ⟨⟨proj Λ (toE v), proj_mem Λ _⟩, proj_toE_mem_ΓW v, hnorm, fun w => hrecon w⟩

end ExistsGen


section Inject

variable {Λ : Submodule ℤ (Fin 5 → ℤ)}
variable {b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)}

/-- `uSet Λ T` is finite. -/
lemma uSet_finite (hb : Λ = Submodule.span ℤ (Set.range (pair b)))
    (hli : LinearIndependent ℝ (fun i : Fin 5 => toE (b i))) (T : ℝ) :
    (uSet Λ T).Finite := by
  let g := Wbasis b Λ hb hli
  have hΓg : ΓW Λ = Submodule.span ℤ (Set.range g) := ΓW_eq_span_Wbasis hb hli
  have hfin : (Metric.closedBall (0 : W Λ) T ∩
      ↑(Submodule.span ℤ (Set.range g))).Finite :=
    ZSpan.setFinite_inter g Metric.isBounded_closedBall
  refine hfin.subset ?_
  intro u hu
  obtain ⟨huΓ, huT⟩ := hu
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_eq_norm]
    simpa [Submodule.coe_norm] using huT
  · rw [← hΓg]
    exact huΓ

/-- The canonical map from a superlattice to the generator of `π(L)`. -/
noncomputable def psi (b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ))
    (Λ : Submodule ℤ (Fin 5 → ℤ)) (hb : Λ = Submodule.span ℤ (Set.range (pair b)))
    (hli : LinearIndependent ℝ (fun i : Fin 5 => toE (b i)))
    (h5 : (Matrix.gram ℝ (fun i : Fin 5 => toE (b i))).det = 1)
    (hΛrk : rk Λ = 2) (hpr : IsPrimLat Λ) (T : ℝ)
    (L : Submodule ℤ (Fin 5 → ℤ)) : W Λ := by
  classical
  exact if h : L ∈ Sset Λ T then Classical.choose (exists_gen hb hli h5 hΛrk hpr h) else 0

lemma psi_spec (hb : Λ = Submodule.span ℤ (Set.range (pair b)))
    (hli : LinearIndependent ℝ (fun i : Fin 5 => toE (b i)))
    (h5 : (Matrix.gram ℝ (fun i : Fin 5 => toE (b i))).det = 1)
    (hΛrk : rk Λ = 2) (hpr : IsPrimLat Λ) {T : ℝ} {L : Submodule ℤ (Fin 5 → ℤ)}
    (hL : L ∈ Sset Λ T) :
    psi b Λ hb hli h5 hΛrk hpr T L ∈ uSet Λ T ∧
      ∀ w : Fin 5 → ℤ, w ∈ L ↔ ∃ m : ℤ,
        proj Λ (toE w) = m • (psi b Λ hb hli h5 hΛrk hpr T L : E5) := by
  have hspec := Classical.choose_spec (exists_gen hb hli h5 hΛrk hpr hL)
  rw [psi]
  simp only [dif_pos hL]
  exact ⟨⟨hspec.1, hspec.2.1⟩, hspec.2.2⟩

/-- Injectivity of `psi` on `Sset`. -/
lemma ncard_Sset_le_uSet (hb : Λ = Submodule.span ℤ (Set.range (pair b)))
    (hli : LinearIndependent ℝ (fun i : Fin 5 => toE (b i)))
    (h5 : (Matrix.gram ℝ (fun i : Fin 5 => toE (b i))).det = 1)
    (hΛrk : rk Λ = 2) (hpr : IsPrimLat Λ) (T : ℝ) :
    (Sset Λ T).ncard ≤ (uSet Λ T).ncard := by
  refine Set.ncard_le_ncard_of_injOn (psi b Λ hb hli h5 hΛrk hpr T) ?_ ?_
    (uSet_finite hb hli T)
  · intro L hL
    exact (psi_spec hb hli h5 hΛrk hpr hL).1
  · intro L hL L' hL' heq
    have h1 := (psi_spec hb hli h5 hΛrk hpr hL).2
    have h2 := (psi_spec hb hli h5 hΛrk hpr hL').2
    ext w
    rw [h1 w, h2 w, heq]

end Inject

section Final

variable {Λ : Submodule ℤ (Fin 5 → ℤ)}
variable {b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)}

/-- The volume of a ball in `W Λ` is at most `7 r ^ 3`. -/
lemma volume_ball_W_le (hb : Λ = Submodule.span ℤ (Set.range (pair b)))
    (hli : LinearIndependent ℝ (fun i : Fin 5 => toE (b i))) (r : ℝ) (hr : 0 ≤ r) :
    (MeasureTheory.volume (Metric.ball (0 : W Λ) r)).toReal ≤ 7 * r ^ 3 := by
  have hconst : Real.sqrt Real.pi ^ 3 / Real.Gamma (3 / 2 + 1) ≤ 7 := by
    have hG : Real.Gamma (3 / 2 + 1) = (3 / 4) * Real.sqrt Real.pi := by
      have h1 : Real.Gamma (3 / 2) = (1 / 2) * Real.sqrt Real.pi := by
        have h := Real.Gamma_add_one (show (1 : ℝ) / 2 ≠ 0 by norm_num)
        rw [show (1 : ℝ) / 2 + 1 = 3 / 2 by norm_num, Real.Gamma_one_half_eq] at h
        linarith
      have h2 := Real.Gamma_add_one (show (3 : ℝ) / 2 ≠ 0 by norm_num)
      rw [show (3 : ℝ) / 2 + 1 = 3 / 2 + 1 by norm_num, h1] at h2
      linarith
    rw [hG, div_le_iff₀ (by positivity)]
    have h3 : Real.sqrt Real.pi ^ 3 = Real.pi * Real.sqrt Real.pi := by
      have h : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
      calc Real.sqrt Real.pi ^ 3 = Real.sqrt Real.pi ^ 2 * Real.sqrt Real.pi := by ring
        _ = Real.pi * Real.sqrt Real.pi := by rw [h]
    rw [h3]
    nlinarith [Real.pi_lt_four, Real.sqrt_pos.mpr Real.pi_pos]
  haveI : Nontrivial ↥(W Λ) :=
    nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_W hb hli]; norm_num)
  rw [InnerProductSpace.volume_ball]
  rw [show Module.finrank ℝ (W Λ) = 3 from finrank_W hb hli]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal (by positivity)]
  have h3 : (0 : ℝ) ≤ r ^ 3 := by positivity
  calc r ^ 3 * (Real.sqrt Real.pi ^ 3 / Real.Gamma (3 / 2 + 1)) ≤ r ^ 3 * 7 :=
        mul_le_mul_of_nonneg_left hconst h3
    _ = 7 * r ^ 3 := by ring

/-- The number of elements of `Sset Λ T` is at most `1000 T^3 detL Λ`. -/
theorem ncard_Sset_le (hb : Λ = Submodule.span ℤ (Set.range (pair b)))
    (hli : LinearIndependent ℝ (fun i : Fin 5 => toE (b i)))
    (h5 : (Matrix.gram ℝ (fun i : Fin 5 => toE (b i))).det = 1)
    (hΛrk : rk Λ = 2) (hpr : IsPrimLat Λ) {T : ℝ} (hT : 1 ≤ T) :
    ((Sset Λ T).ncard : ℝ) ≤ 1000 * T ^ 3 * detL Λ := by
  have hΓg : ΓW Λ = Submodule.span ℤ (Set.range (Wbasis b Λ hb hli)) := ΓW_eq_span_Wbasis hb hli
  haveI : DiscreteTopology ↥(Submodule.span ℤ (Set.range (Wbasis b Λ hb hli))) := inferInstance
  haveI : IsZLattice ℝ (Submodule.span ℤ (Set.range (Wbasis b Λ hb hli))) := inferInstance
  -- the covering property
  have hcov : ∀ x : (W Λ), ∃ u : ↥(Submodule.span ℤ (Set.range (Wbasis b Λ hb hli))),
      ‖x - (u : (W Λ))‖ ≤ Real.sqrt 5 / 2 := by
    intro x
    obtain ⟨u, huΓ, hu⟩ := exists_close_ΓW x
    exact ⟨⟨u, by rw [← hΓg]; exact huΓ⟩, by simpa [Submodule.coe_norm] using hu⟩
  have hcount : ((latBall (Submodule.span ℤ (Set.range (Wbasis b Λ hb hli))) T).ncard : ℝ)
      ≤ (MeasureTheory.volume (Metric.closedBall (0 : (W Λ)) (T + Real.sqrt 5 / 2))).toReal /
        ZLattice.covolume (Submodule.span ℤ (Set.range (Wbasis b Λ hb hli))) :=
    lattice_count_le (L := Submodule.span ℤ (Set.range (Wbasis b Λ hb hli))) hcov
  -- identify the counting set with `uSet`
  have hset : ((latBall (Submodule.span ℤ (Set.range (Wbasis b Λ hb hli))) T).ncard : ℝ)
      = ((uSet Λ T).ncard : ℝ) := by
    have hcongr := Set.ncard_congr
      (s := latBall (Submodule.span ℤ (Set.range (Wbasis b Λ hb hli))) T)
      (t := uSet Λ T)
      (fun u _ => (u : (W Λ)))
      (fun u hu => by
        refine ⟨?_, ?_⟩
        · rw [hΓg]; exact u.2
        · simpa [Submodule.coe_norm] using hu)
      (fun u v _ _ huv => Subtype.ext huv)
      (fun v hv => ⟨⟨v, by rw [← hΓg]; exact hv.1⟩,
        by simpa [Submodule.coe_norm] using hv.2, rfl⟩)
    exact_mod_cast hcongr
  -- covolume
  have hcovol : ZLattice.covolume (Submodule.span ℤ (Set.range (Wbasis b Λ hb hli)))
      = 1 / detL Λ := by
    rw [← hΓg]
    exact covolume_ΓW hb hli h5
  -- the injection
  have hinj : ((Sset Λ T).ncard : ℝ) ≤ ((uSet Λ T).ncard : ℝ) := by
    exact_mod_cast ncard_Sset_le_uSet hb hli h5 hΛrk hpr T
  have hdetpos : 0 < detL Λ := detL_pos hb hli
  -- volume bound : the closed ball of radius `r` sits inside the ball of radius `r + 1`
  have hmono : (MeasureTheory.volume (Metric.closedBall (0 : (W Λ)) (T + Real.sqrt 5 / 2))).toReal
      ≤ (MeasureTheory.volume (Metric.ball (0 : (W Λ)) (T + Real.sqrt 5 / 2 + 1))).toReal := by
    refine ENNReal.toReal_mono ?_ (MeasureTheory.measure_mono ?_)
    · exact ne_of_lt Metric.isBounded_ball.measure_lt_top
    · intro y hy
      rw [Metric.mem_closedBall] at hy
      rw [Metric.mem_ball]
      linarith
  have hvol : (MeasureTheory.volume (Metric.ball (0 : (W Λ)) (T + Real.sqrt 5 / 2 + 1))).toReal
      ≤ 7 * (T + Real.sqrt 5 / 2 + 1) ^ 3 :=
    volume_ball_W_le (b := b) hb hli _ (by linarith [Real.sqrt_nonneg 5, hT])
  have hmain : ((uSet Λ T).ncard : ℝ) ≤ 7 * (T + Real.sqrt 5 / 2 + 1) ^ 3 * detL Λ := by
    rw [← hset]
    have h1 : ((latBall (Submodule.span ℤ (Set.range (Wbasis b Λ hb hli))) T).ncard : ℝ)
        ≤ (MeasureTheory.volume (Metric.closedBall (0 : (W Λ)) (T + Real.sqrt 5 / 2))).toReal * detL Λ := by
      have h := hcount
      rw [hcovol, div_div_eq_mul_div, div_one] at h
      exact h
    calc ((latBall (Submodule.span ℤ (Set.range (Wbasis b Λ hb hli))) T).ncard : ℝ)
        ≤ (MeasureTheory.volume (Metric.closedBall (0 : (W Λ)) (T + Real.sqrt 5 / 2))).toReal * detL Λ := h1
      _ ≤ (MeasureTheory.volume (Metric.ball (0 : (W Λ)) (T + Real.sqrt 5 / 2 + 1))).toReal * detL Λ :=
            mul_le_mul_of_nonneg_right hmono hdetpos.le
      _ ≤ (7 * (T + Real.sqrt 5 / 2 + 1) ^ 3) * detL Λ :=
            mul_le_mul_of_nonneg_right hvol hdetpos.le
      _ = 7 * (T + Real.sqrt 5 / 2 + 1) ^ 3 * detL Λ := by ring
  -- arithmetic
  have hsqrt5 : Real.sqrt 5 / 2 ≤ 6 / 5 := by
    rw [div_le_iff₀ (by norm_num)]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  have hbnd : (T + Real.sqrt 5 / 2 + 1) ^ 3 ≤ (4096 / 125) * T ^ 3 := by
    have h1 : T + Real.sqrt 5 / 2 + 1 ≤ 16 / 5 * T := by nlinarith [hsqrt5, hT]
    have h2 : (0 : ℝ) ≤ T + Real.sqrt 5 / 2 + 1 := by linarith [Real.sqrt_nonneg 5, hT]
    calc (T + Real.sqrt 5 / 2 + 1) ^ 3 ≤ (16 / 5 * T) ^ 3 := pow_le_pow_left₀ h2 h1 3
      _ = (4096 / 125) * T ^ 3 := by ring
  have hdet_nn : (0 : ℝ) ≤ detL Λ := le_of_lt hdetpos
  calc ((Sset Λ T).ncard : ℝ) ≤ ((uSet Λ T).ncard : ℝ) := hinj
    _ ≤ 7 * (T + Real.sqrt 5 / 2 + 1) ^ 3 * detL Λ := hmain
    _ ≤ 7 * ((4096 / 125) * T ^ 3) * detL Λ := by
        have h7 : (0 : ℝ) ≤ 7 * detL Λ := by positivity
        calc 7 * (T + Real.sqrt 5 / 2 + 1) ^ 3 * detL Λ
            = 7 * detL Λ * (T + Real.sqrt 5 / 2 + 1) ^ 3 := by ring
          _ ≤ 7 * detL Λ * ((4096 / 125) * T ^ 3) := mul_le_mul_of_nonneg_left hbnd h7
          _ = 7 * ((4096 / 125) * T ^ 3) * detL Λ := by ring
    _ ≤ 1000 * T ^ 3 * detL Λ := by
        have h9 : (7 : ℝ) * ((4096 : ℝ) / 125) ≤ 1000 := by norm_num
        have h8 : (0 : ℝ) ≤ T ^ 3 := by positivity
        have hTd : (0 : ℝ) ≤ T ^ 3 * detL Λ := mul_nonneg h8 hdet_nn
        calc 7 * ((4096 : ℝ) / 125 * T ^ 3) * detL Λ
            = (7 * ((4096 : ℝ) / 125)) * (T ^ 3 * detL Λ) := by ring
          _ ≤ 1000 * (T ^ 3 * detL Λ) := mul_le_mul_of_nonneg_right h9 hTd
          _ = 1000 * T ^ 3 * detL Λ := by ring

end Final

end

end Work.HP.Q44Child
