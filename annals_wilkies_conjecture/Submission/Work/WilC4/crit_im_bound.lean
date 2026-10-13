/-
  WilC4/crit_im_bound : uniform finiteness of the *image* family `ImFib Y a b c`.

  `unifFinite_of_omin` (via `exists_alt_bound`) bounds the number of order-convex components
  of the fibres of any `LRc`-definable family, provided o-minimality of every model of `TR`.
  Here we observe that the image family

      `ImFam : (a, b, c) ↦ ImFib Y a b c = {y | ∃ x, a < x < b ∧ (x, y, c) ∈ Y}`

  is itself a definable family of subsets of the line (its defining formula is obtained by
  existentially quantifying the point `x` of the interval), so the same bound applies.

  Concretely we write the fibre variable as the summand `Sum.inr 0` of `Fin (k+2) ⊕ Fin 1` and
  the parameters `(a, b, c)` as the summand `Sum.inl`, and exhibit the family as
  `FibFam Y = {f | f (Sum.inr 0) ∈ ImFib Y (f (Sum.inl 0)) (f (Sum.inl 1)) (fun i => f (Sum.inl (i+2)))}`.
  `FibFam Y` is the projection of the ∅-definable set `ImUnproj Y` (the graph of the relation
  `a < x < b ∧ (x,y,c) ∈ Y`) along the witness `x`.
-/
import Mathlib
import Submission.Work.WilC4.CritDefs
import Submission.Work.WilC4.unifFinite_of_omin
import Submission.Work.WilC2.bnd_definable_alt

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The coordinate map `(a,b,c,y) ↦ (x,y,c)` -/

/-- `imMap k` reads off the point `(x, y, c)` of `ℝ^{k+2}` from the block of variables
`(a, b, c) ⊕ y ⊕ x`: `a` is forgotten, the witness `x` becomes the first coordinate, `y` the
second, and `c` the remaining ones. -/
def imMap (k : ℕ) : Fin (k + 2) → ((Fin (k + 2) ⊕ Fin 1) ⊕ Fin 1) :=
  Fin.cons (Sum.inr (0 : Fin 1))
    (Fin.cons (Sum.inl (Sum.inr (0 : Fin 1)))
      (fun i : Fin k => Sum.inl (Sum.inl i.succ.succ)))

@[simp] lemma imMap_zero (k : ℕ) : imMap k 0 = Sum.inr (0 : Fin 1) := by simp [imMap]

@[simp] lemma imMap_succ_succ (k : ℕ) (i : Fin k) :
    imMap k i.succ.succ = Sum.inl (Sum.inl i.succ.succ) := by simp [imMap]

/-- Precomposition with `imMap k` turns an assignment `(a,b,c) ⊕ y ⊕ x` into the point
`(x, y, c)` of `ℝ^{k+2}`. -/
lemma elim_comp_imMap {k : ℕ} (f : (Fin (k + 2) ⊕ Fin 1) → ℝ) (u : Fin 1 → ℝ) :
    (Sum.elim f u) ∘ imMap k =
      Fin.cons (u 0) (Fin.cons (f (Sum.inr (0 : Fin 1)))
        (fun i : Fin k => f (Sum.inl i.succ.succ))) := by
  funext j
  induction j using Fin.cases with
  | zero => simp
  | succ j' =>
      induction j' using Fin.cases with
      | zero => simp [imMap]
      | succ i => simp [imMap]

/-! ## 2. The set before and after projecting out the witness `x` -/

/-- `ImUnproj Y`: the graph of the relation "`a < x < b` and `(x,y,c) ∈ Y`", over the block of
variables `(a, b, c) ⊕ y ⊕ x`. -/
def ImUnproj {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) :
    Set (((Fin (k + 2) ⊕ Fin 1) ⊕ Fin 1) → ℝ) :=
  {g | (g (Sum.inl (Sum.inl (0 : Fin (k + 2)))) < g (Sum.inr (0 : Fin 1)) ∧
        g (Sum.inr (0 : Fin 1)) < g (Sum.inl (Sum.inl (1 : Fin (k + 2))))) ∧
      g ∘ imMap k ∈ Y}

/-- `FibFam Y`: the family of sets `ImFib Y a b c`, with `(a,b,c)` in the `Sum.inl` variables and
the value `y` in the variable `Sum.inr 0`. -/
def FibFam {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) : Set ((Fin (k + 2) ⊕ Fin 1) → ℝ) :=
  {f | f (Sum.inr (0 : Fin 1)) ∈
      ImFib Y (f (Sum.inl (0 : Fin (k + 2)))) (f (Sum.inl (1 : Fin (k + 2))))
        (fun i : Fin k => f (Sum.inl i.succ.succ))}

/-- `ImUnproj Y` is ∅-definable as soon as `Y` is. -/
lemma imUnproj_definable {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (∅ : Set ℝ).Definable LRc (ImUnproj Y) := by
  have hsq : ∀ x : ℝ, 0 ≤ x → ∃ z : ℝ, x = z * z :=
    fun x hx => ⟨Real.sqrt x, by nlinarith [Real.sq_sqrt hx]⟩
  have hlt1 : (∅ : Set ℝ).Definable LRc
      {v : (((Fin (k + 2)) ⊕ Fin 1) ⊕ Fin 1) → ℝ |
        v (Sum.inl (Sum.inl (0 : Fin (k + 2)))) < v (Sum.inr (0 : Fin 1))} :=
    WilC2.definable_lt (A := (∅ : Set ℝ)) hsq
      (Sum.inl (Sum.inl (0 : Fin (k + 2)))) (Sum.inr (0 : Fin 1))
  have hlt2 : (∅ : Set ℝ).Definable LRc
      {v : (((Fin (k + 2)) ⊕ Fin 1) ⊕ Fin 1) → ℝ |
        v (Sum.inr (0 : Fin 1)) < v (Sum.inl (Sum.inl (1 : Fin (k + 2))))} :=
    WilC2.definable_lt (A := (∅ : Set ℝ)) hsq
      (Sum.inr (0 : Fin 1)) (Sum.inl (Sum.inl (1 : Fin (k + 2))))
  have hpre : (∅ : Set ℝ).Definable LRc
      {g : (((Fin (k + 2)) ⊕ Fin 1) ⊕ Fin 1) → ℝ | g ∘ imMap k ∈ Y} :=
    hY.preimage_comp (imMap k)
  exact (hlt1.inter hlt2).inter hpre

/-- The membership condition of `ImUnproj` in coordinates. -/
lemma mem_imUnproj {k : ℕ} (Y : Set (Fin (k + 2) → ℝ))
    (f : (Fin (k + 2) ⊕ Fin 1) → ℝ) (u : Fin 1 → ℝ) :
    (Sum.elim f u ∈ ImUnproj Y) ↔
      ((f (Sum.inl (0 : Fin (k + 2))) < u 0 ∧ u 0 < f (Sum.inl (1 : Fin (k + 2)))) ∧
        Fin.cons (u 0) (Fin.cons (f (Sum.inr (0 : Fin 1)))
          (fun i : Fin k => f (Sum.inl i.succ.succ))) ∈ Y) := by
  simp only [ImUnproj, Set.mem_setOf_eq]
  rw [elim_comp_imMap]
  simp

/-- Projecting out the witness `x` from `ImUnproj Y` gives the fibre family `FibFam Y`. -/
lemma fibFam_eq_proj {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) :
    {v : (Fin (k + 2) ⊕ Fin 1) → ℝ | ∃ u : Fin 1 → ℝ, Sum.elim v u ∈ ImUnproj Y}
      = FibFam Y := by
  ext f
  simp only [Set.mem_setOf_eq, FibFam, ImFib, CGr]
  constructor
  · rintro ⟨u, hu⟩
    rw [mem_imUnproj] at hu
    exact ⟨u 0, hu.1.1, hu.1.2, hu.2⟩
  · rintro ⟨x, h1, h2, h3⟩
    exact ⟨fun _ => x, (mem_imUnproj Y f (fun _ => x)).mpr ⟨⟨h1, h2⟩, h3⟩⟩

/-! ## 3. The uniform bound -/

theorem crit_im_bound {k : ℕ} (hOM : WilkiesDesign.CG.OMinModels) (Y : Set (Fin (k + 2) → ℝ))
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    ∃ N : ℕ, ∀ (a b : ℝ) (c : Fin k → ℝ), ¬ AltChain N (ImFib Y a b c) := by
  have hU : (∅ : Set ℝ).Definable LRc (ImUnproj Y) := imUnproj_definable hY
  have hproj : (∅ : Set ℝ).Definable LRc (FibFam Y) := by
    have h := hU.exists_of_finite
    rwa [fibFam_eq_proj Y] at h
  obtain ⟨φ, hφ⟩ := Set.empty_definable_iff.mp hproj
  have hSmem : ∀ f : (Fin (k + 2) ⊕ Fin 1) → ℝ, f ∈ FibFam Y ↔ φ.Realize f := by
    intro f
    simp only [hφ, Set.mem_ofPred_eq]
  obtain ⟨N, hN⟩ := exists_alt_bound hOM φ
  refine ⟨N, fun a b c => ?_⟩
  have hp := hN (Fin.cons a (Fin.cons b c))
  have hset : {t : ℝ |
        φ.Realize (Sum.elim (Fin.cons a (Fin.cons b c)) (fun _ : Fin 1 => t))}
      = ImFib Y a b c := by
    ext t
    rw [Set.mem_ofPred_eq]
    rw [← hSmem (Sum.elim (Fin.cons a (Fin.cons b c)) (fun _ : Fin 1 => t))]
    simp only [Set.mem_setOf_eq, FibFam]
    have h0 : (Sum.elim (Fin.cons a (Fin.cons b c)) (fun _ : Fin 1 => t)) (Sum.inr (0 : Fin 1))
        = t := by simp
    have h1 : (Sum.elim (Fin.cons a (Fin.cons b c)) (fun _ : Fin 1 => t))
        (Sum.inl (0 : Fin (k + 2))) = a := by simp
    have h2 : (Sum.elim (Fin.cons a (Fin.cons b c)) (fun _ : Fin 1 => t))
        (Sum.inl (1 : Fin (k + 2))) = b := by simp
    have h3 : (fun i : Fin k => (Sum.elim (Fin.cons a (Fin.cons b c))
        (fun _ : Fin 1 => t)) (Sum.inl i.succ.succ)) = c := by
      funext i
      simp
    simp only [h0, h1, h2, h3]
  rw [hset] at hp
  exact hp

end Work.WilC4
