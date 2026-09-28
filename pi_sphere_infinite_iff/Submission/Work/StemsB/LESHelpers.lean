import Mathlib
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.PiMap

/-!
# Tools for the long exact homotopy sequence of a Serre fibration

Cube bookkeeping (`Fin.cons`/`Fin.tail`), the "top face" of a lift of a cube, and the key
uniqueness-of-lifts lemma: two lifts of the same based cube which agree on the bottom face and on
the lateral boundary have homotopic top faces.  This is the lemma that makes the connecting map
`π_{k+2}(B) → π_{k+1}(F)` well defined.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.StemsB

noncomputable section

open Classical

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

/-! ## Cube bookkeeping -/

theorem cons_mem_boundary_iff {n : ℕ} {t : I} {x : Fin n → I} :
    (Fin.cons t x ∈ Cube.boundary (Fin (n+1))) ↔ (t = 0 ∨ t = 1) ∨ x ∈ Cube.boundary (Fin n) := by
  constructor
  · rintro ⟨i, hi⟩
    cases i using Fin.cases with
    | zero => exact Or.inl (by simpa using hi)
    | succ j => exact Or.inr ⟨j, by simpa using hi⟩
  · rintro (h|h)
    · exact ⟨0, by simpa using h⟩
    · obtain ⟨i, hi⟩ := h; exact ⟨i.succ, by simpa using hi⟩

theorem cons_mem_boundary {n : ℕ} {t : I} {x : Fin n → I} (h : x ∈ Cube.boundary (Fin n)) :
    Fin.cons t x ∈ Cube.boundary (Fin (n+1)) := by
  obtain ⟨i, hi⟩ := h; exact ⟨i.succ, by simpa using hi⟩

theorem cons_zero_mem_boundary {n : ℕ} (x : Fin n → I) :
    Fin.cons (0:I) x ∈ Cube.boundary (Fin (n+1)) := ⟨0, Or.inl rfl⟩

theorem cons_one_mem_boundary {n : ℕ} (x : Fin n → I) :
    Fin.cons (1:I) x ∈ Cube.boundary (Fin (n+1)) := ⟨0, Or.inr rfl⟩

theorem tail_mem_boundary_of_cons {n : ℕ} {w : Fin (n+1) → I}
    (hw : w ∈ Cube.boundary (Fin (n+1))) (h0 : w 0 ≠ 0) (h1 : w 0 ≠ 1) :
    Fin.tail w ∈ Cube.boundary (Fin n) := by
  obtain ⟨i, hi⟩ := hw
  cases i using Fin.cases with
  | zero => exact absurd hi (by rintro (h|h); exacts [h0 h, h1 h])
  | succ j => exact ⟨j, by simpa [Fin.tail] using hi⟩

/-- `Fin.tail` is continuous. -/
theorem continuous_finTail (n : ℕ) :
    Continuous fun (q : Fin (n+1) → I) => Fin.tail q := by
  apply continuous_pi
  intro i
  simpa [Fin.tail] using continuous_apply i.succ

/-- `Fin.cons` as a continuous map `I^n × I → I^{n+1}` (appending a last coordinate). -/
def consCM (n : ℕ) : C((Fin n → I) × I, (Fin (n+1) → I)) where
  toFun q := Fin.cons q.2 q.1
  continuous_toFun := by
    apply continuous_pi
    intro i
    cases i using Fin.cases with
    | zero => show Continuous fun q : (Fin n → I) × I => q.2; exact continuous_snd
    | succ j => show Continuous fun q : (Fin n → I) × I => q.1 j
                exact (continuous_apply j).comp continuous_fst

@[simp] theorem consCM_apply (n : ℕ) (q : (Fin n → I) × I) :
    consCM n q = Fin.cons q.2 q.1 := rfl

/-! ## The top face of a lift -/

/-- The top face `x ↦ G (x, 1)` of a lift `G` of a cube `H` whose top face is constantly `p e₀`,
as a map into the fibre `p ⁻¹' {p e₀}`. -/
def topFace {p : C(E, B)} {e₀ : E} (k : ℕ) (H : C((Fin k → I) × I, B))
    (hH1 : ∀ x : Fin k → I, H (x, 1) = p e₀)
    (G : C((Fin k → I) × I, E)) (hG : p.comp G = H) :
    C(Fin k → I, fibre p (p e₀)) where
  toFun x := ⟨G (x, 1), (ContinuousMap.congr_fun hG (x, 1)).trans (hH1 x)⟩
  continuous_toFun := Continuous.subtype_mk (G.continuous.comp (continuous_id.prodMk continuous_const)) _

@[simp] theorem topFace_coe {p : C(E, B)} {e₀ : E} (k : ℕ) (H : C((Fin k → I) × I, B))
    (hH1 : ∀ x : Fin k → I, H (x, 1) = p e₀)
    (G : C((Fin k → I) × I, E)) (hG : p.comp G = H) (x : Fin k → I) :
    ((topFace k H hH1 G hG) x).1 = G (x, 1) := rfl

/-- The top face as an element of the homotopy group `π_k` of the fibre. -/
def topFaceG {p : C(E, B)} {e₀ : E} (k : ℕ) (H : C((Fin k → I) × I, B))
    (hH1 : ∀ x : Fin k → I, H (x, 1) = p e₀)
    (G : C((Fin k → I) × I, E)) (hG : p.comp G = H)
    (hGbd : ∀ (x : CubeBdry k) (t : I), G (x.1, t) = e₀) :
    GenLoop (Fin k) (fibre p (p e₀)) (fibrePoint p e₀) :=
  ⟨topFace k H hH1 G hG, fun x hx => Subtype.ext (hGbd ⟨x, hx⟩ 1)⟩

@[simp] theorem topFaceG_coe {p : C(E, B)} {e₀ : E} (k : ℕ) (H : C((Fin k → I) × I, B))
    (hH1 : ∀ x : Fin k → I, H (x, 1) = p e₀)
    (G : C((Fin k → I) × I, E)) (hG : p.comp G = H)
    (hGbd : ∀ (x : CubeBdry k) (t : I), G (x.1, t) = e₀) :
    (topFaceG k H hH1 G hG hGbd).1 = topFace k H hH1 G hG := rfl

/-! ## Uniqueness of lifts -/

section Uniqueness

variable (p : C(E, B)) (e₀ : E)

/-- **Uniqueness of lifts up to homotopy.**  Let `H : I^k × I → B` be a cube which is constantly
`p e₀` on the bottom face `I^k × {0}` and on the top face `I^k × {1}`.  Let `G₁, G₂` be two lifts
of `H` which are constantly `e₀` on the bottom face and on the lateral boundary `∂I^k × I`.  Then
their top faces are homotopic relative to `∂I^k`.

The proof is one application of the relative homotopy lifting property for the cube `I^{k+1} × I`:
the "interpolation coordinate" `β : I` is a new cube coordinate, and the prescribed lateral lift is
`G₁` for `β ≤ 1/2` and `G₂` for `β ≥ 1/2` (a continuous map: where the two branches meet, the cube
point lies in `∂I^k`, and there both lifts are `e₀`). -/
theorem liftUniqueness (hrel : ∀ k, HasHLPRel p k) (k : ℕ)
    (H : C((Fin k → I) × I, B))
    (hH0 : ∀ x : Fin k → I, H (x, 0) = p e₀)
    (hH1 : ∀ x : Fin k → I, H (x, 1) = p e₀)
    (G₁ G₂ : C((Fin k → I) × I, E))
    (hG₁ : p.comp G₁ = H) (hG₂ : p.comp G₂ = H)
    (hG₁0 : ∀ x : Fin k → I, G₁ (x, 0) = e₀) (hG₂0 : ∀ x : Fin k → I, G₂ (x, 0) = e₀)
    (hG₁bd : ∀ (x : CubeBdry k) (t : I), G₁ (x.1, t) = e₀)
    (hG₂bd : ∀ (x : CubeBdry k) (t : I), G₂ (x.1, t) = e₀) :
    GenLoop.Homotopic (topFaceG k H hH1 G₁ hG₁ hG₁bd) (topFaceG k H hH1 G₂ hG₂ hG₂bd) := by
  have hG₁' : ∀ xt, p (G₁ xt) = H xt := fun xt => ContinuousMap.congr_fun hG₁ xt
  have hG₂' : ∀ xt, p (G₂ xt) = H xt := fun xt => ContinuousMap.congr_fun hG₂ xt
  have hnorm0 : ((0:I) : ℝ) ≤ 1/2 := by norm_num
  have hnorm1 : ¬ (((1:I) : ℝ) ≤ 1/2) := by norm_num
  -- the ambient cube map
  let Hhas : C((Fin (k+1) → I) × I, B) :=
    ⟨fun q => H (Fin.tail q.1, q.2),
      H.continuous.comp (((continuous_finTail k).comp continuous_fst).prodMk continuous_snd)⟩
  have hHhas : ∀ (w : Fin (k+1) → I) (u : I), Hhas (w, u) = H (Fin.tail w, u) := fun w u => rfl
  -- the lateral lift
  let ghas : C(CubeBdry (k+1) × I, E) :=
    ⟨fun q => if (q.1.1 0 : ℝ) ≤ 1/2 then G₁ (Fin.tail q.1.1, q.2) else G₂ (Fin.tail q.1.1, q.2),
      by
        have hcoord : Continuous fun q : CubeBdry (k+1) × I => (q.1.1 0 : ℝ) :=
          continuous_subtype_val.comp ((continuous_apply 0).comp
            (continuous_subtype_val.comp continuous_fst))
        have htail : Continuous fun q : CubeBdry (k+1) × I => Fin.tail q.1.1 :=
          (continuous_finTail k).comp (continuous_subtype_val.comp continuous_fst)
        have hpair : Continuous fun q : CubeBdry (k+1) × I => (Fin.tail q.1.1, q.2) :=
          htail.prodMk continuous_snd
        apply Continuous.if
        · intro q hq
          have hclosed : IsClosed {q : CubeBdry (k+1) × I | (q.1.1 0 : ℝ) ≤ 1/2} :=
            isClosed_Iic.preimage hcoord
          have hqle : (q.1.1 0 : ℝ) ≤ 1/2 := by
            have h1 : q ∈ closure {q : CubeBdry (k+1) × I | (q.1.1 0 : ℝ) ≤ 1/2} := hq.1
            rwa [hclosed.closure_eq] at h1
          have hqe : (q.1.1 0 : ℝ) = 1/2 := by
            refine le_antisymm hqle ?_
            by_contra hlt
            have hlt' : (q.1.1 0 : ℝ) < 1/2 := lt_of_not_ge hlt
            have : q ∈ interior {q : CubeBdry (k+1) × I | (q.1.1 0 : ℝ) ≤ 1/2} := by
              apply mem_interior_iff_mem_nhds.mpr
              have hop : IsOpen {q : CubeBdry (k+1) × I | (q.1.1 0 : ℝ) < 1/2} :=
                isOpen_lt hcoord continuous_const
              refine Filter.mem_of_superset (hop.mem_nhds hlt') ?_
              intro y hy
              exact le_of_lt (show (y.1.1 0 : ℝ) < 1/2 from hy)
            exact hq.2 this
          have hb : Fin.tail q.1.1 ∈ Cube.boundary (Fin k) := by
            refine tail_mem_boundary_of_cons q.1.2 ?_ ?_
            · intro h; rw [h] at hqe; norm_num at hqe
            · intro h; rw [h] at hqe; norm_num at hqe
          rw [hG₁bd ⟨_, hb⟩ q.2, hG₂bd ⟨_, hb⟩ q.2]
        · exact G₁.continuous.comp hpair
        · exact G₂.continuous.comp hpair⟩
  have hghas : ∀ (w : CubeBdry (k+1)) (u : I),
      ghas (w, u) = if (w.1 0 : ℝ) ≤ 1/2 then G₁ (Fin.tail w.1, u)
        else G₂ (Fin.tail w.1, u) := fun w u => rfl
  -- the lifting data
  have hf : p.comp (ContinuousMap.const (Fin (k+1) → I) e₀) = Hhas.comp (zeroIncl (k+1)) := by
    ext w
    show p e₀ = Hhas (w, 0)
    rw [hHhas]
    exact (hH0 _).symm
  have hg : p.comp ghas = Hhas.comp (bdryIncl (k+1)) := by
    ext q
    show p (ghas q) = Hhas (q.1.1, q.2)
    rw [hghas q.1 q.2, hHhas]
    by_cases h : (q.1.1 0 : ℝ) ≤ 1/2
    · rw [if_pos h]; exact hG₁' (Fin.tail q.1.1, q.2)
    · rw [if_neg h]; exact hG₂' (Fin.tail q.1.1, q.2)
  have hg0 : ∀ (x : CubeBdry (k+1)),
      ghas (x, 0) = (ContinuousMap.const (Fin (k+1) → I) e₀) x.1 := by
    intro x
    rw [hghas x 0]
    by_cases h : (x.1 0 : ℝ) ≤ 1/2
    · rw [if_pos h]; exact hG₁0 _
    · rw [if_neg h]; exact hG₂0 _
  obtain ⟨Ψ, hΨp, hΨ0, hΨbd⟩ := hrel (k+1) Hhas (ContinuousMap.const (Fin (k+1) → I) e₀) hf
    ghas hg hg0
  have hΨp' : ∀ q, p (Ψ q) = Hhas q := fun q => ContinuousMap.congr_fun hΨp q
  -- the interpolating homotopy
  have hΦ_cont : Continuous fun q : (Fin k → I) × I => Ψ (consCM k q, 1) :=
    Ψ.continuous.comp ((consCM k).continuous.prodMk continuous_const)
  let Φ : C((Fin k → I) × I, E) := ⟨fun q => Ψ (consCM k q, 1), hΦ_cont⟩
  have hΦ : ∀ q : (Fin k → I) × I, Φ q = Ψ (Fin.cons q.2 q.1, 1) := fun q => rfl
  have hΦmem : ∀ q : (Fin k → I) × I, p (Φ q) = p e₀ := by
    intro q
    rw [hΦ, hΨp', hHhas, Fin.tail_cons, hH1]
  -- the homotopy itself
  refine ⟨ContinuousMap.HomotopyWith.mk
    (ContinuousMap.Homotopy.mk ⟨fun s => ⟨Φ (s.2, s.1), hΦmem (s.2, s.1)⟩, ?_⟩ ?_ ?_) ?_⟩
  · exact (Continuous.subtype_mk (hΦ_cont.comp (continuous_snd.prodMk continuous_fst)) _)
  · -- map_zero_left
    intro x
    apply Subtype.ext
    have hmem : Fin.cons (0:I) x ∈ Cube.boundary (Fin (k+1)) := cons_zero_mem_boundary x
    show Φ (x, 0) = G₁ (x, 1)
    rw [hΦ, hΨbd ⟨Fin.cons (0:I) x, hmem⟩ 1, hghas ⟨Fin.cons (0:I) x, hmem⟩ 1]
    simp only [Fin.cons_zero, Fin.tail_cons]
    rw [if_pos hnorm0]
  · -- map_one_left
    intro x
    apply Subtype.ext
    have hmem : Fin.cons (1:I) x ∈ Cube.boundary (Fin (k+1)) := cons_one_mem_boundary x
    show Φ (x, 1) = G₂ (x, 1)
    rw [hΦ, hΨbd ⟨Fin.cons (1:I) x, hmem⟩ 1, hghas ⟨Fin.cons (1:I) x, hmem⟩ 1]
    simp only [Fin.cons_zero, Fin.tail_cons]
    rw [if_neg hnorm1]
  · -- the homotopy is constant on the boundary
    intro t x hx
    apply Subtype.ext
    have hmem : Fin.cons t x ∈ Cube.boundary (Fin (k+1)) := cons_mem_boundary hx
    show Φ (x, t) = G₁ (x, 1)
    rw [hΦ, hΨbd ⟨Fin.cons t x, hmem⟩ 1, hghas ⟨Fin.cons t x, hmem⟩ 1]
    simp only [Fin.cons_zero, Fin.tail_cons]
    by_cases h : (t : ℝ) ≤ 1/2
    · rw [if_pos h]
    · rw [if_neg h, hG₂bd ⟨x, hx⟩ 1, hG₁bd ⟨x, hx⟩ 1]

end Uniqueness

end

end Work.StemsB
