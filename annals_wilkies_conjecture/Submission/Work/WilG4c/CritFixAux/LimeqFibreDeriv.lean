/-
  WilG4c / CritFixAux / `LimeqFibreDeriv` — the graph of the *fibre* (slice) derivative lies in
  the closed punctured-limit set of the *joint* derivative graph.

  This is a self-contained copy of the content of `Submission/Work/WilG4c/MemLimeqPDgSet.lean`
  (whose own build currently exceeds its heartbeat budget), with the heartbeat budget raised.

  Contents: if `y ↦ f (parPt w) y` is `C^m` at `cubePt w`, then
  `(w, ∂^m_V f(parPt w,·)(cubePt w)) ∈ LimeqP p n (dgSet p n f m V)`, i.e. the values of the
  joint `m`-th derivative along the punctured cube tend to the fibre derivative at `cubePt w`.
-/
import Mathlib
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG4c.SliceDerivJointSubset
import Submission.Work.WilG4c.iterDir_eq_iteratedFDeriv

set_option maxHeartbeats 4000000
set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c.CritFixAux

/-- Transport of the evaluated iterated derivative along an equality of the index. -/
private lemma iteratedFDeriv_congr_fin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m m' : ℕ} (h : m = m')
    (f : E → ℝ) (x : E) (v : Fin m → E) (w : Fin m' → E)
    (hw : ∀ i : Fin m, w (Fin.cast h i) = v i) :
    iteratedFDeriv ℝ m f x v = iteratedFDeriv ℝ m' f x w := by
  subst h
  congr 1
  funext i
  exact (hw i).symm

/-- The iterated directional derivative along the coordinate directions of a tuple `v` is the
iterated Fréchet derivative evaluated on the same directions. -/
private lemma iterDir_ofFn' {N m : ℕ} (v : Fin m → Fin N) (G : (Fin N → ℝ) → ℝ)
    (z : Fin N → ℝ) (hG : ContDiffAt ℝ m G z) :
    Work.WilkG4c.iterDir (List.ofFn v) G z = iteratedFDeriv ℝ m G z (fun k => Pi.single (v k) 1) := by
  have hG' : ContDiffAt ℝ (List.ofFn v).length G z := by
    rw [List.length_ofFn]; exact hG
  rw [Work.WilG4c.iterDir_eq_iteratedFDeriv (List.ofFn v) G z hG']
  refine iteratedFDeriv_congr_fin List.length_ofFn G z
    (fun k => Pi.single ((List.ofFn v).get k) 1) (fun k => Pi.single (v k) 1) (fun i => ?_)
  congr 1
  rw [List.get_ofFn]

/-- The same as `iterDir_ofFn'`, with the tuple pushed forward along a map `φ` of coordinates. -/
private lemma iterDir_ofFn_map {N M m : ℕ} (φ : Fin M → Fin N) (V : Fin m → Fin M)
    (G : (Fin N → ℝ) → ℝ) (z : Fin N → ℝ) (hG : ContDiffAt ℝ m G z) :
    Work.WilkG4c.iterDir ((List.ofFn V).map φ) G z =
      iteratedFDeriv ℝ m G z (fun k => Pi.single (φ (V k)) 1) := by
  rw [List.map_ofFn]
  exact iterDir_ofFn' (fun k => φ (V k)) G z hG

/-- The parameter part of a concatenation is its first factor. -/
private lemma parPt_finAppend {p n : ℕ} (l : Fin p → ℝ) (u : Fin (n + 1) → ℝ) :
    Work.WilkG4c.parPt (Fin.append l u) = l := by
  funext i
  simp [Work.WilkG4c.parPt, Fin.append_left]

/-- The cube part of a concatenation is its second factor. -/
private lemma cubePt_finAppend {p n : ℕ} (l : Fin p → ℝ) (u : Fin (n + 1) → ℝ) :
    Work.WilkG4c.cubePt (Fin.append l u) = u := by
  funext j
  simp [Work.WilkG4c.cubePt, Fin.append_right]

theorem LimeqFibreDeriv {p n m : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (w : Fin (p + (n + 1)) → ℝ)
    (V : Fin m → Fin (n + 1))
    (h : ContDiffAt ℝ m (fun y : Fin (n + 1) → ℝ => f (Work.WilkG4c.parPt w) y)
      (Work.WilkG4c.cubePt w)) :
    Fin.snoc w (iteratedFDeriv ℝ m (fun y : Fin (n + 1) → ℝ => f (Work.WilkG4c.parPt w) y)
        (Work.WilkG4c.cubePt w) (fun i => Pi.single (V i) 1))
      ∈ Work.WilG4c.LimeqP p n (Work.WilkG4c.dgSet p n f m V) := by
  set sl : (Fin (n + 1) → ℝ) → ℝ := fun y => f (Work.WilkG4c.parPt w) y with hsl
  -- The evaluated iterated derivative of the fixed slice is continuous at the cube point.
  have hcont : ContinuousAt
      (fun x : Fin (n + 1) → ℝ => iteratedFDeriv ℝ m sl x (fun i => Pi.single (V i) 1))
      (Work.WilkG4c.cubePt w) := by
    set v : Fin m → (Fin (n + 1) → ℝ) := fun i => (Pi.single (V i) (1 : ℝ) : Fin (n + 1) → ℝ)
      with hv
    set c : Fin (n + 1) → ℝ := Work.WilkG4c.cubePt w with hc
    have h0 : ContinuousAt (iteratedFDeriv ℝ m sl) c :=
      h.continuousAt_iteratedFDeriv le_rfl
    rw [Metric.continuousAt_iff] at h0 ⊢
    intro ε hε
    have hC : (0 : ℝ) ≤ ∏ i : Fin m, ‖v i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
    have hpos : 0 < ∏ i : Fin m, ‖v i‖ + 1 := by linarith
    obtain ⟨δ, hδpos, hδ⟩ := h0 (ε / (∏ i : Fin m, ‖v i‖ + 1)) (by positivity)
    refine ⟨δ, hδpos, fun x hx => ?_⟩
    have h1 : ‖iteratedFDeriv ℝ m sl x - iteratedFDeriv ℝ m sl c‖
        < ε / (∏ i : Fin m, ‖v i‖ + 1) := by
      simpa [dist_eq_norm] using hδ hx
    have hb := ContinuousMultilinearMap.le_opNorm
      (iteratedFDeriv ℝ m sl x - iteratedFDeriv ℝ m sl c) v
    have h2 : ‖iteratedFDeriv ℝ m sl x v - iteratedFDeriv ℝ m sl c v‖
        ≤ ‖iteratedFDeriv ℝ m sl x - iteratedFDeriv ℝ m sl c‖ * ∏ i : Fin m, ‖v i‖ := by
      rw [sub_apply] at hb; exact hb
    rw [dist_eq_norm]
    calc ‖iteratedFDeriv ℝ m sl x v - iteratedFDeriv ℝ m sl c v‖
        ≤ ‖iteratedFDeriv ℝ m sl x - iteratedFDeriv ℝ m sl c‖ * (∏ i : Fin m, ‖v i‖) := h2
      _ ≤ ‖iteratedFDeriv ℝ m sl x - iteratedFDeriv ℝ m sl c‖ * (∏ i : Fin m, ‖v i‖ + 1) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); linarith
      _ < (ε / (∏ i : Fin m, ‖v i‖ + 1)) * (∏ i : Fin m, ‖v i‖ + 1) :=
          mul_lt_mul_of_pos_right h1 hpos
      _ = ε := by field_simp
  simp only [Work.WilG4c.LimeqP]
  rw [Set.mem_ofPred_eq]
  simp only [Fin.init_snoc, Fin.snoc_last]
  intro ε hε
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδpos, hδ⟩ := hcont ε hε
  refine ⟨δ, hδpos, ?_⟩
  intro x _hx hxδ v hv
  -- Unfold the `dgSet` membership: a joint derivative value over the joint `C^m`-locus.
  have hzloc : Fin.append (Work.WilkG4c.parPt w) x ∈
      interior {u : Fin (p + (n + 1)) → ℝ | ContDiffAt ℝ m (Work.WilkG4c.famFunHat f) u} := by
    have h1 := hv
    simp only [Work.WilkG4c.dgSet, Work.WilkG4c.jLoc, Set.mem_setOf_eq] at h1
    simp only [Fin.snoc_last, Fin.init_snoc] at h1
    exact h1.1
  have hzval : v = iteratedFDeriv ℝ m (Work.WilkG4c.famFunHat f)
      (Fin.append (Work.WilkG4c.parPt w) x) (fun i => Pi.single (Fin.natAdd p (V i)) 1) := by
    have h1 := hv
    simp only [Work.WilkG4c.dgSet, Work.WilkG4c.jLoc, Set.mem_setOf_eq] at h1
    simp only [Fin.init_snoc, Fin.snoc_last] at h1
    exact h1.2
  have hc : ContDiffAt ℝ m (Work.WilkG4c.famFunHat f) (Fin.append (Work.WilkG4c.parPt w) x) :=
    interior_subset hzloc
  -- Joint ⟹ fibre: the joint derivative over the joint locus is the fibre derivative.
  have hsz : Fin.init (Fin.snoc (Fin.append (Work.WilkG4c.parPt w) x) v
        : Fin (p + (n + 1) + 1) → ℝ) ∈
      interior {u : Fin (p + (n + 1)) → ℝ |
        ContDiffAt ℝ (List.ofFn V).length (Work.WilkG4c.famFunHat f) u} := by
    rw [Fin.init_snoc, List.length_ofFn]
    exact hzloc
  obtain ⟨hslice, hval⟩ := Work.WilG4c.SliceDerivJointSubset f (List.ofFn V)
    (Fin.snoc (Fin.append (Work.WilkG4c.parPt w) x) v : Fin (p + (n + 1) + 1) → ℝ) hsz
  have hslice_x : ContDiffAt ℝ (List.ofFn V).length
      (fun y : Fin (n + 1) → ℝ => f (Work.WilkG4c.parPt w) y) x := by
    simpa only [Fin.init_snoc, parPt_finAppend, cubePt_finAppend]
      using hslice
  have hslice_len : ContDiffAt ℝ (List.ofFn V).length sl x := by
    simpa only [hsl] using hslice_x
  have hslice_m : ContDiffAt ℝ m sl x := by
    rw [List.length_ofFn] at hslice_x
    simpa only [hsl] using hslice_x
  -- The `dgSet`-value at the cube point `x` is the fibre derivative there.
  have hvG : v = iteratedFDeriv ℝ m sl x (fun i => Pi.single (V i) 1) := by
    rw [hzval]
    rw [Fin.init_snoc] at hval
    rw [parPt_finAppend, cubePt_finAppend] at hval
    rw [← hsl] at hval
    calc iteratedFDeriv ℝ m (Work.WilkG4c.famFunHat f) (Fin.append (Work.WilkG4c.parPt w) x)
          (fun i => Pi.single (Fin.natAdd p (V i)) 1)
        = Work.WilkG4c.iterDir ((List.ofFn V).map (Fin.natAdd p)) (Work.WilkG4c.famFunHat f)
            (Fin.append (Work.WilkG4c.parPt w) x) :=
          (iterDir_ofFn_map (Fin.natAdd p) V (Work.WilkG4c.famFunHat f)
            (Fin.append (Work.WilkG4c.parPt w) x) hc).symm
      _ = iteratedFDeriv ℝ (List.ofFn V).length sl x
            (fun j => Pi.single ((List.ofFn V).get j) 1) := hval
      _ = Work.WilkG4c.iterDir (List.ofFn V) sl x :=
          (Work.WilG4c.iterDir_eq_iteratedFDeriv (List.ofFn V) sl x hslice_len).symm
      _ = iteratedFDeriv ℝ m sl x (fun k => Pi.single (V k) 1) :=
          iterDir_ofFn' V sl x hslice_m
  -- The continuity bound on the punctured cube.
  have hdist : dist x (Work.WilkG4c.cubePt w) < δ :=
    (dist_pi_lt_iff (f := x) (g := Work.WilkG4c.cubePt w) hδpos).mpr
      (fun j => by rw [Real.dist_eq]; exact hxδ j)
  have hδx := hδ hdist
  rw [hvG]
  rw [Real.dist_eq] at hδx
  exact le_of_lt hδx

end Work.WilkG4c.CritFixAux
