import Submission.Work.BoxShrink.Core.Defs
import Submission.Work.CoreTopology.Winding
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.TorusCover.ParamTorus_exists_liftOf

/-!
# The parameter plane, and the window criterion for inessentiality

The topological core of Pardon's argument is phrased in this development in terms of the
*winding vector* of a closed curve of a parametrised torus
(`Work.CoreTopology.LiftOf`, `Work.SurgeryInvariance.windingOf`): a curve is essential exactly
when its winding vector is nonzero.  This module isolates a completely elementary criterion for
a region `X ⊆ ℝ³` to carry **no** essential loop of the torus `F = P.carrier`, which needs
nothing but the parametrisation itself: the *lift* of a curve of `F` to the parameter plane
`ℝ × ℝ` (through `P.psi`) is a continuous path, and the winding vector is read off from the
displacement of its endpoints over one period.  Consequently, if a lift is confined to a bounded
*rectangular window* of the parameter plane, of side lengths `< 2π` in each coordinate, then its
winding vector vanishes, and it cannot be essential.

This gives the **window criterion** (`not_containsEssentialLoop_of_component_windows` and its
corollary `not_containsEssentialLoop_of_disjoint_windows`): if the preimage `P.psi ⁻¹' X` of a
region of `ℝ³` in the parameter plane is covered by pairwise disjoint *windows* — sets contained
in a rectangle of side length `< 2π` in each coordinate — then `X` carries no essential loop.

The criterion is the engine behind every "this region is inessential" statement in this chapter:
it turns a *quantitative* statement about the parameter plane (a region is confined to a union of
windows) into a *topological* one about the surface, and it requires no classification of
surfaces, no tameness and no general position.

Two remarks on the shape of the criterion.

* The hypothesis is stated for *connected* subsets of the preimage, not merely for the
  components: this is the form in which it is applied (the image of a lift is a connected set),
  and it makes the criterion usable with a cover by *overlapping* windows (only connectedness is
  used, no disjointness).
* The criterion is deliberately *not* an equivalence.  The converse — that a region carrying no
  essential loop has its preimage confined to windows — is false, and the failure is exactly what
  makes Pardon's Lemma 3 delicate; see `README.md`, `BubbleHalfRefuted.lean` and `SlicingLoops.lean`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## Windows in the parameter plane -/

/-- The **parametrisation of the parameter plane**: the map `q ↦ P.psi q.1 q.2` from the plane
to the torus surface.  It is `2πℤ²`-periodic and identifies the plane with the universal cover of
`F`. -/
def Phi (P : Work.CoreTopology.ParamTorus) (q : ℝ × ℝ) : R3 := P.psi q.1 q.2

@[simp] theorem Phi_apply (q : ℝ × ℝ) : Phi P q = P.psi q.1 q.2 := rfl

theorem Phi_continuous : Continuous (Phi P) := P.cont

theorem Phi_mem_carrier (q : ℝ × ℝ) : Phi P q ∈ P.carrier := P.psi_mem_carrier q.1 q.2

/-- The **preimage of a region `X ⊆ ℝ³` in the parameter plane**. -/
def planePreimage (P : Work.CoreTopology.ParamTorus) (X : Set R3) : Set (ℝ × ℝ) :=
  Phi P ⁻¹' X

@[simp] theorem mem_planePreimage {X : Set R3} {q : ℝ × ℝ} :
    q ∈ planePreimage P X ↔ P.psi q.1 q.2 ∈ X := Iff.rfl

/-- The preimage of the torus surface itself is everything. -/
theorem planePreimage_carrier : planePreimage P P.carrier = Set.univ := by
  ext q
  exact ⟨fun _ => Set.mem_univ _, fun _ => P.psi_mem_carrier q.1 q.2⟩

theorem planePreimage_mono {X Y : Set R3} (h : X ⊆ Y) :
    planePreimage P X ⊆ planePreimage P Y :=
  fun _ hq => h hq

/-- A **window** of the parameter plane: a set confined to an open rectangle whose side lengths
are both `< 2π`.  Inside a window, a lift cannot wind: the two coordinates of the lift are
confined to intervals of length `< 2π`, so the displacement over one period of the curve is `0`. -/
def IsWindow (W : Set (ℝ × ℝ)) : Prop :=
  ∃ a b c d : ℝ, b - a < 2 * Real.pi ∧ d - c < 2 * Real.pi ∧
    W ⊆ Set.Ioo a b ×ˢ Set.Ioo c d

/-- The open rectangle `(a,b) × (c,d)` is a window as soon as both side lengths are `< 2π`. -/
theorem isWindow_Ioo {a b c d : ℝ} (hb : b - a < 2 * Real.pi) (hd : d - c < 2 * Real.pi) :
    IsWindow (Set.Ioo a b ×ˢ Set.Ioo c d) :=
  ⟨a, b, c, d, hb, hd, Subset.rfl⟩

theorem IsWindow.subset {W W' : Set (ℝ × ℝ)} (h : IsWindow W) (hsub : W' ⊆ W) : IsWindow W' := by
  obtain ⟨a, b, c, d, hb, hd, hW⟩ := h
  exact ⟨a, b, c, d, hb, hd, hsub.trans hW⟩

/-! ## The winding of a confined lift vanishes -/

/-- **The first coordinate of the winding of a lift confined to an interval of length `< 2π`.**
Over one period, `L.Θ` advances by `(L.winding).1 · 2π`; if its values over the whole line lie in
an interval of length `< 2π`, this increment has absolute value `< 2π`, hence its integer
coefficient vanishes. -/
theorem winding_fst_eq_zero_of_bdd {γ : Work.CoreTopology.ClosedCurve P}
    (L : Work.CoreTopology.LiftOf P γ) {A B : ℝ} (hAB : B - A < 2 * Real.pi)
    (h : ∀ t : ℝ, A < L.Θ t ∧ L.Θ t < B) : (L.winding).1 = 0 := by
  have hspec := L.winding_spec.1
  have h0 := h 0
  have hπ := h (2 * Real.pi)
  have hbd : |L.Θ (2 * Real.pi) - L.Θ 0| < B - A := by
    rw [abs_lt]; exact ⟨by linarith [hπ.1, h0.2], by linarith [hπ.2, h0.1]⟩
  have heq : L.Θ (2 * Real.pi) - L.Θ 0 = ((L.winding).1 : ℝ) * (2 * Real.pi) := by
    rw [hspec]; ring
  have : |((L.winding).1 : ℝ) * (2 * Real.pi)| < 2 * Real.pi := by
    rw [← heq]; linarith [hbd, hAB]
  have habs : |((L.winding).1 : ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
    rwa [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at this
  have hlt : |((L.winding).1 : ℝ)| < 1 := by
    nlinarith [habs, Real.pi_pos]
  have : |(L.winding).1| < 1 := by exact_mod_cast hlt
  exact Int.abs_lt_one_iff.mp this

/-- **The winding of a lift confined to an interval of length `< 2π` in the meridian
coordinate** (the second coordinate of the winding vector). -/
theorem winding_snd_eq_zero_of_bdd {γ : Work.CoreTopology.ClosedCurve P}
    (L : Work.CoreTopology.LiftOf P γ) {A B : ℝ} (hAB : B - A < 2 * Real.pi)
    (h : ∀ t : ℝ, A < L.Φ t ∧ L.Φ t < B) : (L.winding).2 = 0 := by
  have hspec := L.winding_spec.2
  have h0 := h 0
  have hπ := h (2 * Real.pi)
  have hbd : |L.Φ (2 * Real.pi) - L.Φ 0| < B - A := by
    rw [abs_lt]; exact ⟨by linarith [hπ.1, h0.2], by linarith [hπ.2, h0.1]⟩
  have heq : L.Φ (2 * Real.pi) - L.Φ 0 = ((L.winding).2 : ℝ) * (2 * Real.pi) := by
    rw [hspec]; ring
  have : |((L.winding).2 : ℝ) * (2 * Real.pi)| < 2 * Real.pi := by
    rw [← heq]; linarith [hbd, hAB]
  have habs : |((L.winding).2 : ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
    rwa [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at this
  have hlt : |((L.winding).2 : ℝ)| < 1 := by
    nlinarith [habs, Real.pi_pos]
  have : |(L.winding).2| < 1 := by exact_mod_cast hlt
  exact Int.abs_lt_one_iff.mp this

/-- **A lift whose image lies in a window has vanishing winding vector.** -/
theorem winding_eq_zero_of_window {γ : Work.CoreTopology.ClosedCurve P}
    (L : Work.CoreTopology.LiftOf P γ) {W : Set (ℝ × ℝ)} (hW : IsWindow W)
    (h : ∀ t : ℝ, (L.Θ t, L.Φ t) ∈ W) : L.winding = 0 := by
  obtain ⟨a, b, c, d, hb, hd, hsub⟩ := hW
  have h1 : (L.winding).1 = 0 := winding_fst_eq_zero_of_bdd L hb
    (fun t => (hsub (h t)).1)
  have h2 : (L.winding).2 = 0 := winding_snd_eq_zero_of_bdd L hd
    (fun t => (hsub (h t)).2)
  exact Prod.ext h1 h2

/-! ## The window criterion -/

/-- **The window criterion.**  If every connected subset of the preimage of `X` in the parameter
plane is contained in a window, then `X` carries no essential loop of the torus.

Indeed, an essential loop `γ` lying in `X` has a lift `L`, whose image is a connected subset of
the preimage of `X` (the image of the connected line `ℝ` under the continuous map `t ↦ (L.Θ t,
L.Φ t)`), hence lies in a window, so its winding vector vanishes — contradicting essentiality. -/
theorem not_containsEssentialLoop_of_component_windows (X : Set R3) (𝒲 : Set (Set (ℝ × ℝ)))
    (hwin : ∀ W ∈ 𝒲, IsWindow W)
    (hcov : ∀ S : Set (ℝ × ℝ), IsConnected S → S ⊆ planePreimage P X → ∃ W ∈ 𝒲, S ⊆ W) :
    ¬ P.ContainsEssentialLoop X := by
  rintro ⟨γ, hess, hγ⟩
  -- a lift of `γ`
  obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf P γ
  -- its image is connected and lies in the preimage of `X`
  have hcont : Continuous fun t : ℝ => (L.Θ t, L.Φ t) := L.contΘ.prodMk L.contΦ
  have hconn : IsConnected (Set.range fun t : ℝ => (L.Θ t, L.Φ t)) :=
    isConnected_range hcont
  have hsub : Set.range (fun t : ℝ => (L.Θ t, L.Φ t)) ⊆ planePreimage P X := by
    rintro _ ⟨t, rfl⟩
    simp only [mem_planePreimage]
    rw [L.lifts t]
    exact hγ t
  obtain ⟨W, hW, hWsub⟩ := hcov _ hconn hsub
  -- its winding therefore vanishes, so the curve is not essential
  have hwind : L.winding = 0 := winding_eq_zero_of_window L (hwin W hW)
    (fun t => hWsub ⟨t, rfl⟩)
  have hne : Work.SurgeryInvariance.windingOf P γ ≠ (0, 0) :=
    (Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P γ).mp hess
  rw [Work.SurgeryInvariance.windingOf_eq P γ L, hwind] at hne
  exact hne rfl

/-- **The window criterion, for a cover by pairwise disjoint *open* windows.**  Then every
connected subset of the preimage lies in one of the windows, so the criterion applies. -/
theorem not_containsEssentialLoop_of_disjoint_windows (X : Set R3) (𝒲 : Set (Set (ℝ × ℝ)))
    (hwin : ∀ W ∈ 𝒲, IsWindow W) (hopen : ∀ W ∈ 𝒲, IsOpen W)
    (hdisj : 𝒲.Pairwise Disjoint) (hcov : planePreimage P X ⊆ ⋃₀ 𝒲) :
    ¬ P.ContainsEssentialLoop X := by
  refine not_containsEssentialLoop_of_component_windows X 𝒲 hwin ?_
  intro S hS hsub
  obtain ⟨p, hp⟩ := hS.1
  have hSmem : S ⊆ ⋃₀ 𝒲 := hsub.trans hcov
  obtain ⟨W, hW, hpW⟩ := Set.mem_sUnion.mp (hSmem hp)
  -- `W` and the union of the other windows are disjoint open sets covering `⋃₀ 𝒲`
  have hWopen : IsOpen W := hopen W hW
  have hOtherOpen : IsOpen (⋃₀ (𝒲 \ {W})) := by
    apply isOpen_sUnion
    rintro W' ⟨hW', _⟩
    exact hopen W' hW'
  have hOtherDisj : Disjoint W (⋃₀ (𝒲 \ {W})) := by
    rw [Set.disjoint_left]
    intro q hq hq'
    obtain ⟨W', ⟨hW', hne⟩, hqW'⟩ := Set.mem_sUnion.mp hq'
    exact (Set.disjoint_left.mp (hdisj hW hW' (Ne.symm hne))) hq hqW'
  have hcover' : (⋃₀ 𝒲) ⊆ W ∪ ⋃₀ (𝒲 \ {W}) := by
    intro q hq
    obtain ⟨W', hW', hqW'⟩ := Set.mem_sUnion.mp hq
    by_cases h : W' = W
    · exact Or.inl (h ▸ hqW')
    · exact Or.inr (Set.mem_sUnion.mpr ⟨W', ⟨hW', by simpa using h⟩, hqW'⟩)
  have hsplit : S ⊆ W ∨ S ⊆ ⋃₀ (𝒲 \ {W}) :=
    IsPreconnected.subset_or_subset (s := S) hWopen hOtherOpen hOtherDisj
      (hSmem.trans hcover') hS.2
  rcases hsplit with hcase | hcase
  · exact ⟨W, hW, hcase⟩
  · exfalso
    obtain ⟨W', ⟨hW', hne⟩, hpW'⟩ := Set.mem_sUnion.mp (hcase hp)
    exact (Set.disjoint_left.mp (hdisj hW hW' (Ne.symm hne))) hpW hpW'
/-! ## The converse of the window criterion -/

/-- **The parametrisation of `F` is invariant under `2πℤ²` in the plane.** -/
theorem Phi_add_int (n m : ℤ) (x y : ℝ) :
    Phi P (x + (n : ℝ) * (2 * Real.pi), y + (m : ℝ) * (2 * Real.pi)) = Phi P (x, y) :=
  (P.psi_eq_iff _ _ _ _).mpr ⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩

/-- The same in the pair form used below. -/
theorem Phi_add_lattice {k l : ℤ} (z : ℝ × ℝ) :
    Phi P (z + ((k : ℝ) * (2 * Real.pi), (l : ℝ) * (2 * Real.pi))) = Phi P z :=
  Phi_add_int k l z.1 z.2

/-- **A path with a nonzero period in the preimage gives an essential loop.**  This is the
converse of the window criterion (`not_containsEssentialLoop_of_component_windows`), and it makes
the criterion exact: `X` carries an essential loop of `F` exactly when its preimage in the
parameter plane contains a path whose endpoints differ by a nonzero element of `2πℤ²`.

The path is taken on all of `ℝ`, periodic up to the shift `(k·2π, l·2π) ≠ 0`.  Then
`t ↦ Phi P (q (t / 2π))` is a `2π`-periodic continuous loop of `F` lying in `X`, and `q (t / 2π)`
is a lift of it; its winding vector is `(k, l)` by `winding_spec`, hence nonzero. -/
theorem containsEssentialLoop_of_periodicPath {X : Set R3} {q : ℝ → ℝ × ℝ} (hq : Continuous q)
    {k l : ℤ}
    (hper : ∀ t : ℝ, q (t + 1) = q t + ((k : ℝ) * (2 * Real.pi), (l : ℝ) * (2 * Real.pi)))
    (hne : (k, l) ≠ 0) (hmem : ∀ t : ℝ, Phi P (q t) ∈ X) :
    P.ContainsEssentialLoop X := by
  have htwopi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  set L : ℝ → ℝ × ℝ := fun t => q (t / (2 * Real.pi)) with hL
  have hLcont : Continuous L := hq.comp (continuous_id.div_const _)
  have hperL : ∀ t : ℝ, L (t + 2 * Real.pi) = L t +
      ((k : ℝ) * (2 * Real.pi), (l : ℝ) * (2 * Real.pi)) := by
    intro t
    have harg : (t + 2 * Real.pi) / (2 * Real.pi) = t / (2 * Real.pi) + 1 := by
      field_simp
    simp only [hL, harg]
    exact hper _
  have hperγ : ∀ t : ℝ, Phi P (L (t + 2 * Real.pi)) = Phi P (L t) := by
    intro t; rw [hperL t]; exact Phi_add_lattice (P := P) (L t)
  let γ : Work.CoreTopology.ClosedCurve P :=
    { γ := fun t => Phi P (L t), cont := (Phi_continuous (P := P)).comp hLcont, periodic := hperγ,
      mem := fun t => Phi_mem_carrier (P := P) (L t) }
  let Λ : Work.CoreTopology.LiftOf P γ :=
    { Θ := fun t => (L t).1, Φ := fun t => (L t).2, contΘ := continuous_fst.comp hLcont,
      contΦ := continuous_snd.comp hLcont, lifts := fun _ => rfl }
  have hΘ : Λ.Θ (2 * Real.pi) = Λ.Θ 0 + (k : ℝ) * (2 * Real.pi) := by
    have h := congrArg Prod.fst (hperL 0)
    simpa [Λ, hL] using h
  have hΦ : Λ.Φ (2 * Real.pi) = Λ.Φ 0 + (l : ℝ) * (2 * Real.pi) := by
    have h := congrArg Prod.snd (hperL 0)
    simpa [Λ, hL] using h
  have hw1 : (Λ.winding).1 = k := by
    have h := Λ.winding_spec.1
    rw [hΘ] at h
    have h' : (((Λ.winding).1 : ℤ) : ℝ) * (2 * Real.pi) = (k : ℝ) * (2 * Real.pi) := by
      linarith
    exact_mod_cast mul_right_cancel₀ htwopi h'
  have hw2 : (Λ.winding).2 = l := by
    have h := Λ.winding_spec.2
    rw [hΦ] at h
    have h' : (((Λ.winding).2 : ℤ) : ℝ) * (2 * Real.pi) = (l : ℝ) * (2 * Real.pi) := by
      linarith
    exact_mod_cast mul_right_cancel₀ htwopi h'
  refine ⟨γ, ?_, fun t => hmem (t / (2 * Real.pi))⟩
  rw [Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero,
    Work.SurgeryInvariance.windingOf_eq P γ Λ]
  intro hzero
  have hk : k = 0 := by rw [← hw1, hzero]
  have hl : l = 0 := by rw [← hw2, hzero]
  exact hne (by rw [hk, hl]; rfl)

end

end Work.BoxShrink.Pinch
