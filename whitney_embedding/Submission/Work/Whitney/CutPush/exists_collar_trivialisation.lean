import Mathlib
import Submission.Work.Whitney.CollarLensSeparation
import Submission.Work.Whitney.CutPush.TubeData
import Submission.Work.Whitney.CutPush.exists_global_diffeo_of_germ
import Submission.Work.Whitney.arc_chart_cover
import Submission.Work.Whitney.CutPush.exists_arc_neighbourhood

/-!
# The collar trivialisation: statement and reduction

`Work.Whitney.CutPush.exists_collar_trivialisation` (below, statement unchanged) is the geometric
input of the collar push: a global trivialisation `(β, θ, Ψ)` of `ℝ^{2n}` over `ℝⁿ × ℝⁿ` whose
second component vanishes on the image of a collar of the arc `γ₂`.

Writing `T := (β, θ)`, the two inverse identities say exactly that `T` is a global `C^∞`
diffeomorphism of `ℝ^{2n}` with `T (f '' U) ⊆ ℝⁿ × {0}`: **the collar is flattened into a
hyperplane**.  The trivialisation itself is then a rewrite (`trivialisation_of_flat_image`), and the
whole geometric content is the existence of the flattening, isolated in
`collarTrivialisation_of_flattening` as the data `(U, L, S, S')`.

The geometric content reduces (choosing the collar `U` thin and using that the image of a *thin*
tube around an arc is flattenable after the arc has been isotoped to a segment) to two classical
ingredients in codimension `≥ 3`, neither of which is available in this Mathlib:

* **arc unknotting**: every embedded arc in `ℝ^m`, `m ≥ 4`, with fixed endpoints is isotopic, rel.
  endpoints, to a straight segment (the self-intersection condition of a generic homotopy of an arc
  has codimension `m - 3 ≥ 1`);
* **untwisting of the framing**: a path of orthonormal `(n-1)`-frames in `ℝ^{2n-1}` can be deformed
  to a constant path (`π₁` of the Stiefel manifold `V_{n-1}(ℝ^{2n-1})` is trivial for `n ≥ 3`).

A direct "sweep" of local flattenings along the arc is *not* available: the processed pieces must be
held fixed by the later steps, which forces the later steps to have vanishing displacement on the
processed *bases*; for a single (or any fixed) linear base this contradicts the fact that no linear
projection is injective on the finger (`CutPush/transverseBaseProjectionAtPoint.lean`, module
docstring), and for varying bases it requires globalising a locally prescribed diffeomorphism
(which is not available: `CutPush/NOTES_hasFingerData_S34.md` §7).
-/

namespace Work.Whitney.CutPush

open scoped BigOperators
/-- **A collar inside a prescribed neighbourhood of the arc's image.**  If `O` is an open
neighbourhood of `f '' (γ '' Icc 0 1)`, then there is an open collar `U` of the arc with
`closure U ⊆ W`, `p, q ∉ U` and `f '' U ⊆ O`.  This is the bookkeeping that lets one choose the
collar of `exists_collar_trivialisation` *thin* (inside any prescribed tube around the arc). -/
theorem exists_collar_inside {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [LocallyCompactSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (hf : Continuous f)
    (γ : ℝ → M) (hγ : Continuous γ) (W : Set M) (hW : IsOpen W)
    (hWγ : γ '' Set.Icc (0 : ℝ) 1 ⊆ W)
    (p q : M) (hp : p ∉ γ '' Set.Icc (0 : ℝ) 1) (hq : q ∉ γ '' Set.Icc (0 : ℝ) 1)
    (O : Set (EuclideanSpace ℝ (Fin (2 * n)))) (hO : IsOpen O)
    (hOγ : γ '' Set.Icc (0 : ℝ) 1 ⊆ f ⁻¹' O) :
    ∃ U : Set M, IsOpen U ∧ γ '' Set.Icc (0 : ℝ) 1 ⊆ U ∧ closure U ⊆ W ∧
      p ∉ U ∧ q ∉ U ∧ f '' U ⊆ O := by
  have hW' : IsOpen (W ∩ f ⁻¹' O) := hW.inter (hO.preimage hf)
  have hsub : γ '' Set.Icc (0 : ℝ) 1 ⊆ W ∩ f ⁻¹' O := fun x hx => ⟨hWγ hx, hOγ hx⟩
  obtain ⟨U, hUo, hUarc, hUsub, hUcl, hpU, hqU⟩ :=
    exists_arc_neighbourhood γ hγ (W ∩ f ⁻¹' O) hW' hsub p q hp hq
  refine ⟨U, hUo, hUarc, fun x hx => (hUcl hx).1, hpU, hqU, ?_⟩
  rintro y ⟨x, hxU, rfl⟩
  exact (hUsub hxU).2


/-- **A flattened collar gives the trivialisation.**  If a global `C^∞` diffeomorphism `S` of
`ℝ^{2n}` (with inverse `S'`) carries `f '' U` into the zero section of a linear splitting `L` of
`ℝ^{2n}` onto `ℝⁿ × ℝⁿ`, then `β := (L ∘ S).₁`, `θ := (L ∘ S).₂` and `Ψ := S' ∘ L.symm` are a
trivialisation with `θ (f x) = 0` for `x ∈ U`. -/
theorem trivialisation_of_flat_image {n : ℕ} {M : Type*}
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (U : Set M)
    (S S' : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
    (hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (hS' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S')
    (hSS' : ∀ y, S' (S y) = y) (hS'S : ∀ y, S (S' y) = y)
    (L : EuclideanSpace ℝ (Fin (2 * n)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (hflat : ∀ x ∈ U, (L (S (f x))).2 = 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (L (S y)).1) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (L (S y)).2) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => S' (L.symm z)) ∧
    (∀ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ((fun y => (L (S y)).1) (S' (L.symm z)), (fun y => (L (S y)).2) (S' (L.symm z))) = z) ∧
    (∀ y : EuclideanSpace ℝ (Fin (2 * n)),
      S' (L.symm ((fun y => (L (S y)).1) y, (fun y => (L (S y)).2) y)) = y) ∧
    (∀ x : M, x ∈ U → (fun y => (L (S y)).2) (f x) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ContinuousLinearEquiv.contDiff L).fst.comp hS
  · exact (ContinuousLinearEquiv.contDiff L).snd.comp hS
  · exact hS'.comp (ContinuousLinearEquiv.contDiff L.symm)
  · intro z
    have h1 : (fun y => (L (S y)).1) (S' (L.symm z)) = (L (S (S' (L.symm z)))).1 := rfl
    have h2 : (fun y => (L (S y)).2) (S' (L.symm z)) = (L (S (S' (L.symm z)))).2 := rfl
    rw [h1, h2, hS'S, ContinuousLinearEquiv.apply_symm_apply]
  · intro y
    have h : ((fun y => (L (S y)).1) y, (fun y => (L (S y)).2) y) = L (S y) := rfl
    rw [h, ContinuousLinearEquiv.symm_apply_apply, hSS']
  · intro x hx
    simpa using hflat x hx

/-- **The collar trivialisation from the flattening data.**  If there is an open collar `U` (with the
clauses of `exists_collar_trivialisation`) together with a global `C^∞` diffeomorphism `(S, S')` of
`ℝ^{2n}` and a linear splitting `L` such that `(L (S (f x))).₂ = 0` for `x ∈ U`, then the full
conclusion of `exists_collar_trivialisation` holds.  This isolates *all* of the geometric content of
the theorem in the existence of the flattening `(U, L, S, S')`. -/
theorem collarTrivialisation_of_flattening {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    {f : M → EuclideanSpace ℝ (Fin (2 * n))}
    {W : Set M} {p₁ p₂ q₁ q₂ : M} {γ : ℝ → M}
    (U : Set M)
    (hU : IsOpen U) (hUcl : closure U ⊆ W) (hUarc : γ '' Set.Icc (0 : ℝ) 1 ⊆ U)
    (hUp₂ : p₂ ∈ U) (hUq₂ : q₂ ∈ U) (hUp₁ : p₁ ∉ U) (hUq₁ : q₁ ∉ U)
    (L : EuclideanSpace ℝ (Fin (2 * n)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (S S' : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
    (hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (hS' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S')
    (hSS' : ∀ y, S' (S y) = y) (hS'S : ∀ y, S (S' y) = y)
    (hflat : ∀ x : M, x ∈ U → (L (S (f x))).2 = 0) :
    ∃ (U : Set M) (β θ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin n))
      (Ψ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin (2 * n))),
      IsOpen U ∧ closure U ⊆ W ∧ γ '' Set.Icc (0 : ℝ) 1 ⊆ U ∧
      p₂ ∈ U ∧ q₂ ∈ U ∧ p₁ ∉ U ∧ q₁ ∉ U ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ ∧
      (∀ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), (β (Ψ z), θ (Ψ z)) = z) ∧
      (∀ y : EuclideanSpace ℝ (Fin (2 * n)), Ψ (β y, θ y) = y) ∧
      (∀ x : M, x ∈ U → θ (f x) = 0) := by
  obtain ⟨hβ, hθ, hΨ, hinv₁, hinv₂, hzero⟩ := trivialisation_of_flat_image f U S S' hS hS' hSS' hS'S L hflat
  exact ⟨U, fun y => (L (S y)).1, fun y => (L (S y)).2, fun z => S' (L.symm z),
    hU, hUcl, hUarc, hUp₂, hUq₂, hUp₁, hUq₁, hβ, hθ, hΨ, hinv₁, hinv₂, hzero⟩

/-! ## The "last mile" of the tube route

The collar trivialisation is, as recorded above, equivalent to the *flattening* of the sheet.  For a
sheet which is a **canonical tube** around a *straight* segment — i.e. the image of
`(s, v) ↦ s • e + ∑ i, v i • B s i` for an orthonormal frame field `B` normal to the direction `e` —
the flattening has an explicit two-step proof which needs no topology at all:

* **frame matching**: a smooth family of linear equivalences `R s` with `R s (B s i) = C i` for a
  fixed orthonormal frame `C` (this is the only non-elementary input, isolated below as a
  hypothesis; it is a self-contained linear-algebra lemma, requested separately);
* **the fibered diffeomorphism** `S (s, u) = (s, R s u)` of `ℝ × ℝ^M`, which is a global `C^∞`
  diffeomorphism with `C^∞` inverse (`fibered_diffeomorphism_of_linearFamily`), and which carries
  the tube into the plane `ℝ × span C` (`tube_cone_flat_of_frame_matching`).

`tube_cone_flat_of_frame_matching` is a *proof* of the flatness statement for canonical tubes, with
the frame-matching family taken as an explicit input. -/

/-- **A smooth family of linear equivalences gives a global diffeomorphism.**

If `R : ℝ → (E ≃L[ℝ] E)` is such that both `(s,u) ↦ R s u` and `(s,u) ↦ (R s).symm u` are `C^∞`,
then `S (s,u) := (s, R s u)` is a bijection of `ℝ × E` with inverse `S' (s,u) := (s, (R s).symm u)`,
and both `S` and `S'` are `C^∞`.  This is the globalization used to flatten a canonical tube. -/
theorem fibered_diffeomorphism_of_linearFamily {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (R : ℝ → E ≃L[ℝ] E)
    (hR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => R p.1 p.2))
    (hRi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => (R p.1).symm p.2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => (p.1, R p.1 p.2)) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => (p.1, (R p.1).symm p.2)) ∧
    (∀ p : ℝ × E, (fun q : ℝ × E => (q.1, R q.1 q.2)) ((fun q => (q.1, (R q.1).symm q.2)) p) = p) ∧
    (∀ p : ℝ × E, (fun q : ℝ × E => (q.1, (R q.1).symm q.2)) ((fun q => (q.1, R q.1 q.2)) p) = p) := by
  refine ⟨contDiff_fst.prodMk hR, contDiff_fst.prodMk hRi, ?_, ?_⟩
  · intro p; simp
  · intro p; simp

/-- **A canonical tube is flattened by a matching family of linear equivalences.**

Let `B s` be an orthonormal `k`-frame in `ℝ^M` and `R s` a family of linear equivalences with
`R s (B s i) = C i` for a fixed orthonormal frame `C`.  Then the fibered diffeomorphism
`(s,u) ↦ (s, R s u)` carries every point of the tube `{ (s, ∑ i, v i • B s i) : v }` into the plane
`{ (s, ∑ i, v i • C i) : v } = ℝ × span C`. -/
theorem tube_cone_flat_of_frame_matching {M k : ℕ}
    (C : Fin k → EuclideanSpace ℝ (Fin M))
    (B : ℝ → Fin k → EuclideanSpace ℝ (Fin M))
    (R : ℝ → EuclideanSpace ℝ (Fin M) ≃L[ℝ] EuclideanSpace ℝ (Fin M))
    (hRB : ∀ s i, R s (B s i) = C i) :
    ∀ s (v : Fin k → ℝ),
      (fun p : ℝ × EuclideanSpace ℝ (Fin M) => (p.1, R p.1 p.2)) (s, ∑ i, v i • B s i)
        = (s, ∑ i, v i • C i) := by
  intro s v
  simp only [Prod.mk.injEq, true_and]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul, hRB]

/-- **A tube is flat as soon as its slices are flattenable by a smooth family.**

Let `Ψ s` be a smooth family of diffeomorphisms of the fibre `ℝ^M` (with smooth inverse family
`Ψ' s`), and let `Γ : ℝ → ℝ^M → ℝ^M` parametrise a sheet over the straight core `ℝ × {0}`.  If every
slice `Γ s '' _` is carried by `Ψ s` into a *fixed* set `P`, then the fibered map
`(s,u) ↦ (s, Ψ s u)` is a global `C^∞` diffeomorphism carrying the sheet into `ℝ × P`.

This isolates the *only* remaining geometric input of the last mile for a general (not necessarily
canonical) tube: the smooth family of slice-diffeomorphisms `Ψ s`. -/
theorem tube_flat_of_slice_flattening {M : ℕ}
    (Γ : ℝ → EuclideanSpace ℝ (Fin M) → EuclideanSpace ℝ (Fin M))
    (Ψ Ψ' : ℝ → EuclideanSpace ℝ (Fin M) → EuclideanSpace ℝ (Fin M))
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin M) => Ψ p.1 p.2))
    (hΨ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin M) => Ψ' p.1 p.2))
    (h1 : ∀ s u, Ψ' s (Ψ s u) = u) (h2 : ∀ s u, Ψ s (Ψ' s u) = u)
    (P : Set (EuclideanSpace ℝ (Fin M)))
    (hflat : ∀ s v, Ψ s (Γ s v) ∈ P) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin M) => (p.1, Ψ p.1 p.2)) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin M) => (p.1, Ψ' p.1 p.2)) ∧
    (∀ p : ℝ × EuclideanSpace ℝ (Fin M),
      (fun q => (q.1, Ψ q.1 q.2)) ((fun q => (q.1, Ψ' q.1 q.2)) p) = p) ∧
    (∀ p : ℝ × EuclideanSpace ℝ (Fin M),
      (fun q => (q.1, Ψ' q.1 q.2)) ((fun q => (q.1, Ψ q.1 q.2)) p) = p) ∧
    (∀ s v, (fun p : ℝ × EuclideanSpace ℝ (Fin M) => (p.1, Ψ p.1 p.2)) (s, Γ s v)
      ∈ Set.univ ×ˢ P) := by
  refine ⟨contDiff_fst.prodMk hΨ, contDiff_fst.prodMk hΨ', ?_, ?_, ?_⟩
  · intro p
    show (p.1, Ψ p.1 (Ψ' p.1 p.2)) = p
    rw [h2 p.1 p.2]
  · intro p
    show (p.1, Ψ' p.1 (Ψ p.1 p.2)) = p
    rw [h1 p.1 p.2]
  · intro s v; exact ⟨trivial, hflat s v⟩


/-! ## The two assembly bricks

The target is reduced (above) to the *flattening data*: an open collar `U` of the arc together with a
global `C^∞` diffeomorphism `A` of `ℝ^{2n}` and a linear splitting `L` such that `(L (A (f x))).₂ = 0`
on `U`.  The following two lemmas isolate the two purely formal steps of the assembly:

* `exists_linearEquiv_vanishing_on`: an `n`-dimensional subspace of `ℝ^{2n}` is the kernel of the
  second component of some linear isomorphism `ℝ^{2n} ≃ ℝⁿ × ℝⁿ`;
* `collarTrivialisation_of_ball`: if the finger `f '' U` is contained in the image of a closed unit
  ball `e` of `ℝⁿ` and that ball can be compressed into an `n`-plane by a global diffeomorphism
  (the codimension-`≥ 3` unknotting input), then the flattening data — hence the target — exists. -/

/-- **A linear splitting vanishing on a prescribed `n`-plane.**  If `K ⊆ ℝ^{2n}` has dimension `n`,
then there is a linear isomorphism `L : ℝ^{2n} ≃ ℝⁿ × ℝⁿ` whose second component vanishes on `K`. -/
theorem exists_linearEquiv_vanishing_on {n : ℕ}
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n)))) (hK : Module.finrank ℝ K = n) :
    ∃ L : EuclideanSpace ℝ (Fin (2 * n)) ≃L[ℝ]
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      ∀ y ∈ K, (L y).2 = 0 := by
  classical
  have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * n))) = 2 * n := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  have horth : Module.finrank ℝ Kᗮ = n := by
    have h := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) K
    rw [hE, hK] at h
    omega
  have hcompl : IsCompl K Kᗮ := Submodule.isCompl_orthogonal K
  have hfn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  have he₁ : K ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearEquiv.ofFinrankEq K (EuclideanSpace ℝ (Fin n)) (by rw [hK, hfn])
  have he₂ : Kᗮ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearEquiv.ofFinrankEq Kᗮ (EuclideanSpace ℝ (Fin n)) (by rw [horth, hfn])
  refine ⟨((K.prodEquivOfIsCompl Kᗮ hcompl).symm.trans
    (LinearEquiv.prodCongr he₁ he₂)).toContinuousLinearEquiv, ?_⟩
  intro y hy
  have hfwd : (K.prodEquivOfIsCompl Kᗮ hcompl) (⟨y, hy⟩, (0 : Kᗮ)) = y := by
    show (y : EuclideanSpace ℝ (Fin (2 * n))) + (0 : Kᗮ) = y
    simp
  have hsym : (K.prodEquivOfIsCompl Kᗮ hcompl).symm y = (⟨y, hy⟩, (0 : Kᗮ)) :=
    (LinearEquiv.symm_apply_eq (e := K.prodEquivOfIsCompl Kᗮ hcompl)).mpr hfwd.symm
  show ((LinearEquiv.prodCongr he₁ he₂)
    ((K.prodEquivOfIsCompl Kᗮ hcompl).symm y)).2 = 0
  rw [hsym]
  simp

/-- **Assembly of the collar trivialisation from a ball chart of the finger.**  If the finger
`f '' U` is contained in the image of the closed unit ball under a smooth embedding
`e : ℝⁿ → ℝ^{2n}` and some global diffeomorphism compresses that ball into an `n`-dimensional
subspace `K`, then the flattening data of `collarTrivialisation_of_flattening` exists, i.e. the
collar trivialisation follows. -/
theorem collarTrivialisation_of_ball {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    {f : M → EuclideanSpace ℝ (Fin (2 * n))} {W : Set M} {p₁ p₂ q₁ q₂ : M} {γ : ℝ → M}
    (U : Set M) (hU : IsOpen U) (hUcl : closure U ⊆ W) (hUarc : γ '' Set.Icc (0 : ℝ) 1 ⊆ U)
    (hUp₂ : p₂ ∈ U) (hUq₂ : q₂ ∈ U) (hUp₁ : p₁ ∉ U) (hUq₁ : q₁ ∉ U)
    (e : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n)))
    (hfinger : f '' U ⊆ e '' Metric.closedBall 0 1)
    (hcomp : ∃ (A Ainv : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
      (K : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n)))),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv ∧
      Function.LeftInverse Ainv A ∧ Function.RightInverse Ainv A ∧
      Module.finrank ℝ K = n ∧
      (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, A (e x) ∈ K)) :
    ∃ (U : Set M) (β θ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin n))
      (Ψ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin (2 * n))),
      IsOpen U ∧ closure U ⊆ W ∧ γ '' Set.Icc (0 : ℝ) 1 ⊆ U ∧
      p₂ ∈ U ∧ q₂ ∈ U ∧ p₁ ∉ U ∧ q₁ ∉ U ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ ∧
      (∀ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), (β (Ψ z), θ (Ψ z)) = z) ∧
      (∀ y : EuclideanSpace ℝ (Fin (2 * n)), Ψ (β y, θ y) = y) ∧
      (∀ x : M, x ∈ U → θ (f x) = 0) := by
  obtain ⟨A, Ainv, K, hAc, hAic, hlinv, hrinv, hKdim, hAK⟩ := hcomp
  obtain ⟨L, hL⟩ := exists_linearEquiv_vanishing_on K hKdim
  refine collarTrivialisation_of_flattening U hU hUcl hUarc hUp₂ hUq₂ hUp₁ hUq₁ L A Ainv
    hAc hAic (fun y => hlinv y) (fun y => hrinv y) ?_
  intro x hx
  have hfx : f x ∈ e '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := hfinger ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hfx
  have h1 : A (e y) = A (f x) := by rw [hyx]
  rw [← h1]
  exact hL (A (e y)) (hAK y hy)

/-- **Injectivity of the finger parametrisation.**  If `f` is injective on `W` up to the two double
points (`hclean`), and the image of `φ` on `s` avoids the two partners `p₁, q₁`, then `f ∘ φ` is
injective on `s`.  This is the step that turns a chart of the finger into a *parametrisation* of a
ball in the target. -/
theorem injOn_comp_of_clean {n : ℕ} {M : Type*}
    {f : M → EuclideanSpace ℝ (Fin (2 * n))} {W : Set M} {p₁ p₂ q₁ q₂ : M}
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    {φ : EuclideanSpace ℝ (Fin n) → M} {s : Set (EuclideanSpace ℝ (Fin n))}
    (hsub : φ '' s ⊆ W) (hp₁ : p₁ ∉ φ '' s) (hq₁ : q₁ ∉ φ '' s)
    (hφ : Set.InjOn φ s) :
    Set.InjOn (fun x => f (φ x)) s := by
  intro x hx y hy hxy
  have hxW : φ x ∈ W := hsub ⟨x, hx, rfl⟩
  have hyW : φ y ∈ W := hsub ⟨y, hy, rfl⟩
  have hxmem : φ x ∈ φ '' s := ⟨x, hx, rfl⟩
  rcases hclean (φ x) (φ y) hxW hyW hxy with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hφ hx hy h
  · exact absurd ⟨x, hx, h1⟩ hp₁
  · exact absurd ⟨y, hy, h2⟩ hp₁
  · exact absurd ⟨x, hx, h1⟩ hq₁
  · exact absurd ⟨y, hy, h2⟩ hq₁

/-- **`f` is already injective away from the two double points.**  On `W ∖ {p₁, q₁}` the cleanliness
hypothesis gives injectivity outright: every collision listed by `hclean` involves `p₁` or `q₁`. -/
theorem injOn_of_clean_sdiff {n : ℕ} {M : Type*}
    {f : M → EuclideanSpace ℝ (Fin (2 * n))} {W : Set M} {p₁ p₂ q₁ q₂ : M}
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁)) :
    Set.InjOn f (W \ {p₁, q₁}) := by
  intro y hy z hz hyz
  have hyW : y ∈ W := hy.1
  have hzW : z ∈ W := hz.1
  have hyne₁ : y ≠ p₁ := fun h => hy.2 (by simp [h])
  have hyne₂ : y ≠ q₁ := fun h => hy.2 (by simp [h])
  have hzne₁ : z ≠ p₁ := fun h => hz.2 (by simp [h])
  have hzne₂ : z ≠ q₁ := fun h => hz.2 (by simp [h])
  rcases hclean y z hyW hzW hyz with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h
  · exact absurd h1 hyne₁
  · exact absurd h2 hzne₁
  · exact absurd h1 hyne₂
  · exact absurd h2 hzne₂


/-- **The collar-flattening input from thin-collar data.**

This is the *interface* lemma: if the classical input (an arbitrarily thin collar of the arc can be
flattened into a hyperplane by a global diffeomorphism) is available for one specific relatively
compact neighbourhood `U₀` of the arc on which `f` is injective and which avoids `p₁, q₁`, then the
whole flattening data of `exists_collar_flattening` follows.  It isolates every piece of bookkeeping
in `exists_collar_flattening` from the geometry. -/
theorem exists_collar_flattening_of_thin_data {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    {f : M → EuclideanSpace ℝ (Fin (2 * n))}
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W)) (p₁ p₂ q₁ q₂ : M)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁))
    (γ : ℝ → M) (hγ0 : γ 0 = p₂) (hγ1 : γ 1 = q₂)
    (U₀ : Set M) (hU₀ : IsOpen U₀) (hU₀inj : Set.InjOn f U₀) (hU₀W : closure U₀ ⊆ W)
    (hp₁U₀ : p₁ ∉ U₀) (hq₁U₀ : q₁ ∉ U₀) (harcU₀ : γ '' Set.Icc (0 : ℝ) 1 ⊆ U₀)
    (H : ∃ U : Set M, IsOpen U ∧ γ '' Set.Icc (0 : ℝ) 1 ⊆ U ∧ closure U ⊆ U₀ ∧
      ∃ (A Ainv : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
        (K : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n)))),
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv ∧
        Function.LeftInverse Ainv A ∧ Function.RightInverse Ainv A ∧
        Module.finrank ℝ K = n ∧ (∀ x : M, x ∈ U → A (f x) ∈ K)) :
    ∃ (U : Set M) (A Ainv : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
      (K : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n)))),
      IsOpen U ∧ closure U ⊆ W ∧ γ '' Set.Icc (0 : ℝ) 1 ⊆ U ∧
      p₂ ∈ U ∧ q₂ ∈ U ∧ p₁ ∉ U ∧ q₁ ∉ U ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv ∧
      Function.LeftInverse Ainv A ∧ Function.RightInverse Ainv A ∧
      Module.finrank ℝ K = n ∧ (∀ x : M, x ∈ U → A (f x) ∈ K) := by
  obtain ⟨U, hUo, harc, hUcl, A, Ainv, K, hAc, hAic, hlinv, hrinv, hK, hfl⟩ := H
  refine ⟨U, A, Ainv, K, hUo, ?_, harc, ?_, ?_, ?_, ?_, hAc, hAic, hlinv, hrinv, hK, hfl⟩
  · exact fun x hx => hU₀W (subset_closure (hUcl hx))
  · rw [← hγ0]
    exact harc ⟨0, Set.left_mem_Icc.mpr (by norm_num), rfl⟩
  · rw [← hγ1]
    exact harc ⟨1, Set.right_mem_Icc.mpr (by norm_num), rfl⟩
  · exact fun hx => hp₁U₀ (hUcl (subset_closure hx))
  · exact fun hx => hq₁U₀ (hUcl (subset_closure hx))

/-- **From a plane-carried collar to the collar trivialisation.** -/
theorem collarTrivialisation_of_plane_image {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    {f : M → EuclideanSpace ℝ (Fin (2 * n))} {W : Set M} {p₁ p₂ q₁ q₂ : M} {γ : ℝ → M}
    (U : Set M) (hU : IsOpen U) (hUcl : closure U ⊆ W) (hUarc : γ '' Set.Icc (0 : ℝ) 1 ⊆ U)
    (hUp₂ : p₂ ∈ U) (hUq₂ : q₂ ∈ U) (hUp₁ : p₁ ∉ U) (hUq₁ : q₁ ∉ U)
    (A Ainv : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hAi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv)
    (hlinv : Function.LeftInverse Ainv A) (hrinv : Function.RightInverse Ainv A)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n)))) (hK : Module.finrank ℝ K = n)
    (hplane : ∀ x : M, x ∈ U → A (f x) ∈ K) :
    ∃ (U : Set M) (β θ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin n))
      (Ψ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin (2 * n))),
      IsOpen U ∧ closure U ⊆ W ∧ γ '' Set.Icc (0 : ℝ) 1 ⊆ U ∧
      p₂ ∈ U ∧ q₂ ∈ U ∧ p₁ ∉ U ∧ q₁ ∉ U ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ ∧
      (∀ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), (β (Ψ z), θ (Ψ z)) = z) ∧
      (∀ y : EuclideanSpace ℝ (Fin (2 * n)), Ψ (β y, θ y) = y) ∧
      (∀ x : M, x ∈ U → θ (f x) = 0) := by
  obtain ⟨L, hL⟩ := exists_linearEquiv_vanishing_on K hK
  exact collarTrivialisation_of_flattening U hU hUcl hUarc hUp₂ hUq₂ hUp₁ hUq₁ L A Ainv
    hA hAi (fun y => hlinv y) (fun y => hrinv y) (fun x hx => hL (A (f x)) (hplane x hx))

/-- **Thin collars suffice.**  If the flattening data can be produced for a collar inside *every*
open neighbourhood `V` of the arc with `closure V ⊆ W`, then `exists_collar_flattening` holds.

This is the reduction that lets a proof of `exists_collar_flattening` work with a *thin* tube around
the arc (and hence, for instance, straighten a smooth approximation of `γ` rather than `γ` itself):
choose `V` by `exists_arc_neighbourhood` and apply the hypothesis to `V`. -/
theorem exists_collar_flattening_of_thin {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [LocallyCompactSpace M]
    {f : M → EuclideanSpace ℝ (Fin (2 * n))}
    (W : Set M) (hWopen : IsOpen W)
    (p₁ p₂ q₁ q₂ : M)
    (γ : ℝ → M) (hγ : Continuous γ) (hγ0 : γ 0 = p₂) (hγ1 : γ 1 = q₂)
    (hγW : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ t ∈ W)
    (hγarc : p₁ ∉ γ '' Set.Icc (0 : ℝ) 1) (hγarc' : q₁ ∉ γ '' Set.Icc (0 : ℝ) 1)
    (hlocal : ∀ V : Set M, IsOpen V → γ '' Set.Icc (0 : ℝ) 1 ⊆ V → closure V ⊆ W →
      ∃ (U : Set M) (A Ainv : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
        (K : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n)))),
        IsOpen U ∧ U ⊆ V ∧ γ '' Set.Icc (0 : ℝ) 1 ⊆ U ∧ p₁ ∉ U ∧ q₁ ∉ U ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv ∧
        Function.LeftInverse Ainv A ∧ Function.RightInverse Ainv A ∧
        Module.finrank ℝ K = n ∧ (∀ x : M, x ∈ U → A (f x) ∈ K)) :
    ∃ (U : Set M) (A Ainv : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
      (K : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n)))),
      IsOpen U ∧ closure U ⊆ W ∧ γ '' Set.Icc (0 : ℝ) 1 ⊆ U ∧
      p₂ ∈ U ∧ q₂ ∈ U ∧ p₁ ∉ U ∧ q₁ ∉ U ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv ∧
      Function.LeftInverse Ainv A ∧ Function.RightInverse Ainv A ∧
      Module.finrank ℝ K = n ∧ (∀ x : M, x ∈ U → A (f x) ∈ K) := by
  have hγW' : γ '' Set.Icc (0 : ℝ) 1 ⊆ W := fun x hx => by
    obtain ⟨t, ht, rfl⟩ := hx
    exact hγW t ht
  obtain ⟨V, hVo, hVarc, _hVsub, hVcl, _hp₁, _hq₁⟩ :=
    exists_arc_neighbourhood γ hγ W hWopen hγW' p₁ q₁ hγarc hγarc'
  obtain ⟨U, A, Ainv, K, hUo, hUV, hUarc, hUp₁, hUq₁, hA, hAi, hlinv, hrinv, hK, hplane⟩ :=
    hlocal V hVo hVarc hVcl
  refine ⟨U, A, Ainv, K, hUo, fun x hx => hVcl (closure_mono hUV hx), hUarc, ?_, ?_,
    hUp₁, hUq₁, hA, hAi, hlinv, hrinv, hK, hplane⟩
  · exact hUarc ⟨0, ⟨le_refl 0, zero_le_one⟩, hγ0⟩
  · exact hUarc ⟨1, ⟨zero_le_one, le_refl 1⟩, hγ1⟩

/-- **A thin tube on which `f` is injective.**  Since `f` is injective on `W ∖ {p₁, q₁}`
(`injOn_of_clean_sdiff`) and the arc avoids `p₁, q₁`, the arc has an open neighbourhood `U` with
`closure U ⊆ W` and `p₁, q₁ ∉ U` on which `f` is injective.  This is the first structural step of
the route to `exists_collar_flattening`: the finger may be taken to be this thin. -/
theorem exists_tube_injOn {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [LocallyCompactSpace M]
    {f : M → EuclideanSpace ℝ (Fin (2 * n))} {W : Set M} {p₁ p₂ q₁ q₂ : M}
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (Wopen : IsOpen W) (γ : ℝ → M) (hγ : Continuous γ)
    (hγW : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ t ∈ W)
    (hγarc : p₁ ∉ γ '' Set.Icc (0 : ℝ) 1) (hγarc' : q₁ ∉ γ '' Set.Icc (0 : ℝ) 1) :
    ∃ U : Set M, IsOpen U ∧ γ '' Set.Icc (0 : ℝ) 1 ⊆ U ∧ closure U ⊆ W ∧
      p₁ ∉ U ∧ q₁ ∉ U ∧ Set.InjOn f U := by
  classical
  have hW''open : IsOpen (W \ {p₁, q₁}) := Wopen.sdiff (Set.Finite.isClosed (by simp))
  have harc'' : γ '' Set.Icc (0 : ℝ) 1 ⊆ W \ {p₁, q₁} := by
    rintro x ⟨t, ht, rfl⟩
    exact ⟨hγW t ht, by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => hγarc ⟨t, ht, h⟩, fun h => hγarc' ⟨t, ht, h⟩⟩⟩
  obtain ⟨U, hUo, hUarc, hUsub, hUcl, hUp₁, hUq₁⟩ :=
    exists_arc_neighbourhood γ hγ (W \ {p₁, q₁}) hW''open harc'' p₁ q₁ hγarc hγarc'
  exact ⟨U, hUo, hUarc, fun x hx => (hUcl hx).1, hUp₁, hUq₁,
    (injOn_of_clean_sdiff hclean).mono hUsub⟩

/-- **Uniform approximation of a continuous map by a `C^∞` map on a compact set.**  The analytic
input of step 1 of the route to `exists_collar_flattening`: `Mathlib`'s mollification theorem
(`Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le`) plus Heine–Cantor on a ball
containing the compact set. -/
theorem exists_contDiff_near {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → F) (hf : Continuous f) {K : Set E} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ ∀ x ∈ K, ‖g x - f x‖ < ε := by
  classical
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  -- `K` lies in the ball of radius `max R 0 + 1`; points within distance `1` of it lie in the ball
  -- of radius `max R 0 + 2`, on which we apply Heine–Cantor
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : E)
  have hRle : R ≤ max R 0 + 1 := by
    have h : R ≤ max R 0 := le_max_left _ _
    linarith
  have hRsub : K ⊆ Metric.closedBall (0 : E) (max R 0 + 1) :=
    fun x hx => Metric.closedBall_subset_closedBall hRle (hR hx)
  have hC : IsCompact (Metric.closedBall (0 : E) (max R 0 + 2)) := isCompact_closedBall _ _
  have hUC : UniformContinuousOn f (Metric.closedBall (0 : E) (max R 0 + 2)) :=
    hC.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨δ, hδpos, hδ⟩ := hUC (ε / 2) hε2
  have hminpos : 0 < min δ 1 := lt_min hδpos one_pos
  set r : ℝ := min δ 1 / 2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hrδ : r < δ := by
    have h1 : min δ 1 ≤ δ := min_le_left _ _
    rw [hrdef]; linarith
  have hr1 : r < 1 := by
    have h1 : min δ 1 ≤ 1 := min_le_right _ _
    rw [hrdef]; linarith
  obtain ⟨g, hg, hgprop⟩ :=
    Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le (f := f) hf hrpos
  refine ⟨g, hg, ?_⟩
  intro x hx
  have hxnorm : ‖x‖ ≤ max R 0 + 1 := by
    have h1 : ‖x‖ ≤ R := by simpa using hR hx
    linarith
  have hkey : ∀ y ∈ Metric.ball x r, dist (f y) (f x) ≤ ε / 2 := by
    intro y hy
    have hxy : dist x y < r := by simpa [dist_comm] using hy
    have hynorm : ‖y‖ ≤ max R 0 + 2 := by
      have h2 : ‖y‖ ≤ ‖x‖ + dist x y := by
        calc ‖y‖ = ‖x + (y - x)‖ := by rw [add_sub_cancel]
          _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
          _ = ‖x‖ + dist x y := by rw [dist_eq_norm, norm_sub_rev]
      linarith
    have hxC : x ∈ Metric.closedBall (0 : E) (max R 0 + 2) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith
    have hyC : y ∈ Metric.closedBall (0 : E) (max R 0 + 2) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hynorm
    have hlt : dist (f x) (f y) < ε / 2 := hδ x hxC y hyC (by linarith)
    rw [dist_comm] at hlt
    exact le_of_lt hlt
  have hgx : dist (g x) (f x) ≤ ε / 2 := hgprop x (ε / 2) hkey
  rw [dist_eq_norm] at hgx
  linarith

theorem exists_contDiff_near_fixing_ends {n : ℕ}
    (f : ℝ → EuclideanSpace ℝ (Fin n)) (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → EuclideanSpace ℝ (Fin n), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      g a = f a ∧ g b = f b ∧ ∀ x ∈ Set.Icc a b, ‖g x - f x‖ < ε := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact ⟨fun _ => f a, contDiff_const, rfl, rfl, fun x hx => by
      have hxb : x = a := le_antisymm hx.2 hx.1
      simp [hxb, hε]⟩
  · have hba : 0 < b - a := by linarith
    have h4 : (0 : ℝ) < ε / 4 := by linarith
    obtain ⟨g₀, hg₀, hg₀near⟩ :=
      exists_contDiff_near f hf (K := Set.Icc a b) isCompact_Icc h4
    -- two bumps with disjoint supports around `a` and `b`
    let ρa : ContDiffBump a := ⟨(b - a) / 6, (b - a) / 3, by linarith, by linarith⟩
    let ρb : ContDiffBump b := ⟨(b - a) / 6, (b - a) / 3, by linarith, by linarith⟩
    have hmem_a : a ∈ Metric.closedBall a ρa.rIn := by
      rw [Metric.mem_closedBall, dist_self]
      exact le_of_lt ρa.rIn_pos
    have hmem_b : b ∈ Metric.closedBall b ρb.rIn := by
      rw [Metric.mem_closedBall, dist_self]
      exact le_of_lt ρb.rIn_pos
    have hρa1 : ρa a = 1 := ContDiffBump.one_of_mem_closedBall (f := ρa) (x := a) hmem_a
    have hρb1 : ρb b = 1 := ContDiffBump.one_of_mem_closedBall (f := ρb) (x := b) hmem_b
    have hρba : ρb a = 0 := by
      refine ContDiffBump.zero_of_le_dist (f := ρb) (x := a) ?_
      have h1 : ρb.rOut = (b - a) / 3 := rfl
      rw [h1, Real.dist_eq, abs_of_neg (by linarith : a - b < 0)]
      linarith
    have hρab : ρa b = 0 := by
      refine ContDiffBump.zero_of_le_dist (f := ρa) (x := b) ?_
      have h1 : ρa.rOut = (b - a) / 3 := rfl
      rw [h1, Real.dist_eq, abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)]
      linarith
    have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ => g₀ x + ρa x • (f a - g₀ a) + ρb x • (f b - g₀ b)) :=
      (hg₀.add ((ρa.contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x => ρa x).smul
        contDiff_const)).add
        ((ρb.contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x => ρb x).smul contDiff_const)
    refine ⟨fun x : ℝ => g₀ x + ρa x • (f a - g₀ a) + ρb x • (f b - g₀ b), hsmooth, ?_, ?_, ?_⟩
    · simp only [hρa1, hρba, one_smul, zero_smul, add_zero]
      abel
    · simp only [hρb1, hρab, one_smul, zero_smul, add_zero]
      abel
    · intro x hx
      have h1 : ‖g₀ x - f x‖ < ε / 4 := hg₀near x hx
      have ha : ‖f a - g₀ a‖ < ε / 4 := by
        have h := hg₀near a (by constructor <;> linarith)
        rwa [norm_sub_rev] at h
      have hb : ‖f b - g₀ b‖ < ε / 4 := by
        have h := hg₀near b (by constructor <;> linarith)
        rwa [norm_sub_rev] at h
      have hρan : |ρa x| ≤ 1 := by
        rw [abs_of_nonneg ρa.nonneg]; exact ρa.le_one
      have hρbn : |ρb x| ≤ 1 := by
        rw [abs_of_nonneg ρb.nonneg]; exact ρb.le_one
      have hnorma : ‖ρa x • (f a - g₀ a)‖ ≤ ε / 4 := by
        rw [norm_smul, Real.norm_eq_abs]
        calc |ρa x| * ‖f a - g₀ a‖ ≤ 1 * ‖f a - g₀ a‖ :=
              mul_le_mul_of_nonneg_right hρan (norm_nonneg _)
          _ = ‖f a - g₀ a‖ := one_mul _
          _ ≤ ε / 4 := le_of_lt ha
      have hnormb : ‖ρb x • (f b - g₀ b)‖ ≤ ε / 4 := by
        rw [norm_smul, Real.norm_eq_abs]
        calc |ρb x| * ‖f b - g₀ b‖ ≤ 1 * ‖f b - g₀ b‖ :=
              mul_le_mul_of_nonneg_right hρbn (norm_nonneg _)
          _ = ‖f b - g₀ b‖ := one_mul _
          _ ≤ ε / 4 := le_of_lt hb
      calc ‖g₀ x + ρa x • (f a - g₀ a) + ρb x • (f b - g₀ b) - f x‖
          = ‖(g₀ x - f x) + ρa x • (f a - g₀ a) + ρb x • (f b - g₀ b)‖ := by abel_nf
        _ ≤ ‖(g₀ x - f x) + ρa x • (f a - g₀ a)‖ + ‖ρb x • (f b - g₀ b)‖ := norm_add_le _ _
        _ ≤ (‖g₀ x - f x‖ + ‖ρa x • (f a - g₀ a)‖) + ‖ρb x • (f b - g₀ b)‖ := by
              linarith [norm_add_le (g₀ x - f x) (ρa x • (f a - g₀ a))]
        _ ≤ (ε / 4 + ε / 4) + ε / 4 := by linarith
        _ < ε := by linarith


/-! ## The finite ordered chain along the arc

`exists_arc_chain` materialises the chain the gluing needs: a *uniform* subdivision of `Icc 0 1`
into `K` pieces, together with, for each piece, a chart centre `t j` and radius `ρ j` such that the
whole piece lies in that chart's ball.  Consecutive pieces share the junction `(j+1)/K`, so the
junction parameters and the overlap regions are named explicitly.

The one *local* input is isolated as a hypothesis (`hlocal`): every point of the arc has a radius
`δ` on which a single chart ball works.  That is the Lebesgue-number step for the pullback cover,
which Mathlib does not provide; it is stated separately as `exists_arc_chain_radius` below. -/
theorem exists_arc_chain {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (γ : ℝ → M) (hγ : Continuous γ) {δ : ℝ} (hδ : 0 < δ)
    (hlocal : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∃ (t ρ : ℝ), 0 < ρ ∧ t ∈ Set.Icc (0 : ℝ) 1 ∧
        Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) (γ t)) (γ t)) ρ ⊆
          (chartAt (EuclideanSpace ℝ (Fin n)) (γ t)).target ∧
        Set.Icc (s - δ) (s + δ) ⊆
          {u : ℝ | γ u ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (γ t)).source ∧
            (chartAt (EuclideanSpace ℝ (Fin n)) (γ t)) (γ u) ∈
              Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) (γ t)) (γ t)) ρ}) :
    ∃ (K : ℕ) (_hK : 0 < K) (t ρ : Fin K → ℝ),
      (∀ j, 0 < ρ j) ∧ (∀ j, t j ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ j, Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))) (γ (t j))) (ρ j) ⊆
        (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))).target) ∧
      ∀ j : Fin K, ∀ s ∈ Set.Icc ((j : ℝ) / K) (((j : ℝ) + 1) / K),
        γ s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))).source ∧
        (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))) (γ s) ∈
          Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))) (γ (t j))) (ρ j) := by
  classical
  -- a number of pieces whose length is at most `δ`
  obtain ⟨K, hKpos, hKδ⟩ : ∃ K : ℕ, 0 < K ∧ (1 : ℝ) / K ≤ δ := by
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    exact ⟨m + 1, Nat.succ_pos m, le_of_lt (by simpa using hm)⟩
  have hKposR : (0 : ℝ) < K := by exact_mod_cast hKpos
  -- the chart data at each midpoint
  choose t ρ htpos htIcc hball hpiece using fun j : Fin K =>
    hlocal (((j : ℝ) + 1 / 2) / K) (by
      constructor
      · have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
        positivity
      · have hj : (j : ℝ) + 1 ≤ K := by
          have := j.isLt
          exact_mod_cast (Nat.succ_le_of_lt this)
        rw [div_le_one hKposR]
        linarith)
  refine ⟨K, hKpos, t, ρ, htpos, htIcc, hball, ?_⟩
  intro j s hs
  -- `s` is within `δ` of the midpoint of the piece
  have h2a : ((j : ℝ) + 1 / 2) / K = (j : ℝ) / K + 1 / 2 / K := by
    rw [add_div]
  have h2b : ((j : ℝ) + 1) / K = ((j : ℝ) + 1 / 2) / K + 1 / 2 / K := by
    have hnum : (j : ℝ) + 1 = ((j : ℝ) + 1 / 2) + 1 / 2 := by ring
    rw [hnum, add_div]
  have hmid : |s - (((j : ℝ) + 1 / 2) / K)| ≤ 1 / 2 / K := by
    rw [abs_le]
    constructor
    · linarith [hs.1, h2a]
    · linarith [hs.2, h2b]
  have hδ' : 1 / 2 / K ≤ δ := by
    have hle : (1 : ℝ) / 2 / K ≤ 1 / K :=
      div_le_div_of_nonneg_right (by norm_num) (le_of_lt hKposR)
    linarith
  have hmem : s ∈ Set.Icc (((j : ℝ) + 1 / 2) / K - δ) (((j : ℝ) + 1 / 2) / K + δ) := by
    rw [Set.mem_Icc]
    have h := abs_le.mp hmid
    constructor <;> linarith
  exact (hpiece j) hmem

/-! ### The local Lebesgue input, proved

`exists_arc_chain_radius` is the local radius fed to `exists_arc_chain`.  Its proof uses
`Work.Whitney.arc_chart_cover` for the chart centres and Mathlib's
`lebesgue_number_lemma_of_metric` (`Topology/MetricSpace/Pseudo/Lemmas.lean`) applied to the compact
`Icc 0 1` and the open cover by the pullback sets
`W i = {u | γ u ∈ chart i.source ∧ ball (chart i (γ (t i))) (ρ i) ⊆ chart i.target
        ∧ chart i (γ u) ∈ ball (chart i (γ i)) (ρ i)}`
(open because the first two clauses are open and the third is constant, so `W i` is either that
intersection or `∅`; `ContinuousOn.isOpen_inter_preimage`, `OpenPartialHomeomorph.continuousOn`
and `Metric.isOpen_ball` supply the openness). -/
theorem exists_arc_chain_radius {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (γ : ℝ → M) (hγ : Continuous γ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ∃ (t ρ : ℝ), 0 < ρ ∧ t ∈ Set.Icc (0 : ℝ) 1 ∧
          Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) (γ t)) (γ t)) ρ ⊆
            (chartAt (EuclideanSpace ℝ (Fin n)) (γ t)).target ∧
          Set.Icc (s - δ) (s + δ) ⊆
            {u : ℝ | γ u ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (γ t)).source ∧
              (chartAt (EuclideanSpace ℝ (Fin n)) (γ t)) (γ u) ∈
                Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) (γ t)) (γ t)) ρ} := by
  classical
  obtain ⟨N, _hN, t, ρ, hρ, ht, hcov⟩ := Work.Whitney.arc_chart_cover (n := n) γ hγ
  -- the pullback cover sets
  set W : Fin N → Set ℝ := fun i =>
    {u : ℝ | γ u ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t i))).source ∧
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) (γ (t i))) (γ (t i))) (ρ i) ⊆
        (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t i))).target ∧
      (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t i))) (γ u) ∈
        Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) (γ (t i))) (γ (t i))) (ρ i)} with hW
  have hWo : ∀ i, IsOpen (W i) := by
    intro i
    by_cases hB : Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) (γ (t i))) (γ (t i))) (ρ i) ⊆
        (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t i))).target
    · have hcont : ContinuousOn
          (fun u : ℝ => (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t i))) (γ u))
          {u : ℝ | γ u ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t i))).source} :=
        ((chartAt (EuclideanSpace ℝ (Fin n)) (γ (t i)))).continuousOn.comp hγ.continuousOn
          (fun u hu => hu)
      have hopen := hcont.isOpen_inter_preimage
        (((chartAt (EuclideanSpace ℝ (Fin n)) (γ (t i)))).open_source.preimage hγ)
        (Metric.isOpen_ball (x := (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t i))) (γ (t i)))
          (ε := ρ i))
      have hset : W i =
          {u : ℝ | γ u ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t i))).source} ∩
            (fun u : ℝ => (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t i))) (γ u)) ⁻¹'
              Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) (γ (t i))) (γ (t i))) (ρ i) := by
        ext u
        simp only [hW, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
        constructor
        · rintro ⟨h1, _h2, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩
          exact ⟨h1, hB, h3⟩
      rw [hset]; exact hopen
    · have hset : W i = ∅ := by
        ext u
        simp only [hW, Set.mem_setOf_eq, Set.mem_empty_iff_false]
        constructor
        · rintro ⟨_h1, h2, _h3⟩
          exact absurd h2 hB
        · intro h
          exact h.elim
      rw [hset]; exact isOpen_empty
  have hcovW : Set.Icc (0 : ℝ) 1 ⊆ ⋃ i, W i := by
    intro u hu
    obtain ⟨i, h1, h2, h3⟩ := hcov u hu
    exact Set.mem_iUnion.mpr ⟨i, h1, h2, h3⟩
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hWo hcovW
  refine ⟨δ₀ / 2, by linarith, ?_⟩
  intro s hs
  obtain ⟨i, hi⟩ := hδ₀ s hs
  have hsW : s ∈ W i := hi (Metric.mem_ball_self hδ₀pos)
  refine ⟨t i, ρ i, hρ i, ht i, hsW.2.1, ?_⟩
  intro u hu
  have hu' : u ∈ Metric.ball s δ₀ := by
    rw [Metric.mem_ball]
    have h1 : |u - s| ≤ δ₀ / 2 := by
      rw [abs_le]
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h2 : dist u s = |u - s| := by
      rw [dist_eq_norm, Real.norm_eq_abs]
    linarith
  exact ⟨(hi hu').1, (hi hu').2.2⟩

/-! ## The first junction

The template for the gluing: for two *adjacent* pieces of the chain (`exists_arc_chain`), the arc is
approximated in each chart by a `C^∞` map with the **same pinned value at the junction**
`(j+1)/K`, the two chartwise pieces agreeing through the chart transition.  The construction is two
applications of `exists_contDiff_near_fixing_ends`; the one technical point is that the chartwise map
`u ↦ c (γ u)` is only continuous (indeed smooth) on the *open* chart-source region, so it must first
be multiplied by a smooth cutoff supported inside that region.

The *push* half of the junction needs nothing new: the workspace already has

* `Work.Whitney.CutPush.slabPush_comp_on_inner` — the composite `ψ₂ ∘ ψ₁` acts on the inner slab of
  the first piece exactly as `ψ₁` does, given (a) `d₂ = 0` off the inner slab `A₂in`, (b) the inner
  slab of the first piece is preserved by its own shear, (c) `H₁ '' A₁in` and `H₂ '' A₂in` are
  disjoint;
* `Work.Whitney.CutPush.slabPush_eq_self_of_vanishes` — the per-piece disjointness tool;
* `Work.Whitney.exists_smooth_bump_slab` — the amplitude whose support is the inner slab (giving
  (a)), and `Work.Whitney.tube_slab_thickening` for the confinement that discharges (c). -/
/-- **Cutoff extension.**  A function that is continuous on an open set `V` can be extended to a
*globally* continuous function agreeing with it on a prescribed compact `P ⊆ V` (multiply by a
Urysohn bump that is `1` on `P` and `0` off a closed thickening of `P` inside `V`).  This is what
lets `exists_contDiff_near_fixing_ends` be applied to a *chartwise* arc piece, which is only
continuous on the open chart-source region. -/
theorem exists_continuous_cutoff_extension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {V : Set ℝ} (hV : IsOpen V) {P : Set ℝ} (hP : IsCompact P) (hPV : P ⊆ V)
    (hf : ContinuousOn f V) :
    ∃ g : ℝ → E, Continuous g ∧ Set.EqOn g f P := by
  classical
  -- a closed thickening of `P` inside `V`
  obtain ⟨δ, hδpos, hδV⟩ := hP.exists_cthickening_subset_open hV hPV
  have hcl : closure (Metric.thickening δ P) ⊆ Metric.cthickening δ P :=
    Metric.closure_thickening_subset_cthickening δ P
  -- Urysohn's two closed sets: the complement of the open thickening, and `P`
  have hSclosed : IsClosed ((Metric.thickening δ P)ᶜ) := Metric.isOpen_thickening.isClosed_compl
  have hdisj : Disjoint (Metric.thickening δ P)ᶜ P := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx (Metric.self_subset_thickening hδpos P hx')
  obtain ⟨χ, hχ0, hχ1, _⟩ :=
    exists_continuous_zero_one_of_isClosed hSclosed hP.isClosed hdisj
  refine ⟨fun u => χ u • f u, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro u
    by_cases hu : u ∈ Metric.cthickening δ P
    · -- inside the thickening: `f` is continuous at `u` because `u ∈ V`
      exact χ.continuous.continuousAt.smul (hf.continuousAt (hV.mem_nhds (hδV hu)))
    · -- outside the thickening: `χ` vanishes on a whole neighbourhood of `u`
      have hu' : u ∉ closure (Metric.thickening δ P) := fun h => hu (hcl h)
      have hnb : (closure (Metric.thickening δ P))ᶜ ∈ nhds u :=
        isClosed_closure.isOpen_compl.mem_nhds hu'
      have hev : ∀ᶠ x in nhds u, χ x = 0 := by
        filter_upwards [hnb] with x hx
        exact hχ0 fun hxc => hx (subset_closure hxc)
      refine ContinuousAt.congr (continuousAt_const (y := (0 : E))) ?_
      filter_upwards [hev] with x hx
      simp [hx]
  · intro u hu
    show χ u • f u = f u
    rw [hχ1 hu]
    simp

theorem exists_junction_approximation {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (γ : ℝ → M) (hγ : Continuous γ) {K : ℕ} (hK : 0 < K) {t ρ : Fin K → ℝ}
    (hpiece : ∀ j : Fin K, ∀ s ∈ Set.Icc ((j : ℝ) / K) (((j : ℝ) + 1) / K),
      γ s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))).source ∧
      (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))) (γ s) ∈
        Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))) (γ (t j))) (ρ j))
    {ε : ℝ} (hε : 0 < ε) (j : Fin K) (hj : (j : ℝ) + 1 < K) :
    ∃ (h₁ h₂ : ℝ → EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h₁ ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h₂ ∧
      h₁ (((j : ℝ) + 1) / K)
        = (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))) (γ (((j : ℝ) + 1) / K)) ∧
      h₂ (((j : ℝ) + 1) / K)
        = (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t ⟨j.1 + 1, by exact_mod_cast hj⟩)))
            (γ (((j : ℝ) + 1) / K)) ∧
      (∀ s ∈ Set.Icc ((j : ℝ) / K) (((j : ℝ) + 1) / K),
        ‖h₁ s - (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))) (γ s)‖ < ε) ∧
      (∀ s ∈ Set.Icc (((j : ℝ) + 1) / K) (((j : ℝ) + 2) / K),
        ‖h₂ s
          - (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t ⟨j.1 + 1, by exact_mod_cast hj⟩)))
              (γ s)‖ < ε) := by
  classical
  have hKposR : (0 : ℝ) < K := by exact_mod_cast hK
  -- the next index, and its interval
  have hj' : j.1 + 1 < K := by exact_mod_cast hj
  have hj'val : (((⟨j.1 + 1, hj'⟩ : Fin K) : ℝ)) = (j : ℝ) + 1 := by
    show (((j.1 + 1 : ℕ)) : ℝ) = ((j.1 : ℕ) : ℝ) + 1
    push_cast
    ring
  have hIcc : Set.Icc (((j : ℝ) + 1) / K) (((j : ℝ) + 2) / K)
      = Set.Icc (((⟨j.1 + 1, hj'⟩ : Fin K) : ℝ) / K)
          ((((⟨j.1 + 1, hj'⟩ : Fin K) : ℝ) + 1) / K) := by
    rw [hj'val]
    congr 1 <;> ring
  -- ## the first piece
  have hV₁ : IsOpen {u : ℝ | γ u ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))).source} :=
    ((chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))).open_source.preimage hγ)
  have hf₁ : ContinuousOn (fun u : ℝ => (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))) (γ u))
      {u : ℝ | γ u ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))).source} :=
    ((chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j)))).continuousOn.comp hγ.continuousOn
      (fun u hu => hu)
  obtain ⟨g₁, hg₁c, hg₁eq⟩ := exists_continuous_cutoff_extension _
    hV₁ isCompact_Icc (fun u hu => (hpiece j u hu).1) hf₁
  have hab₁ : (j : ℝ) / K ≤ ((j : ℝ) + 1) / K :=
    div_le_div_of_nonneg_right (by linarith) (le_of_lt hKposR)
  obtain ⟨h₁, hh₁sm, _hh₁a, hh₁b, hh₁near⟩ :=
    exists_contDiff_near_fixing_ends (a := (j : ℝ) / K) (b := ((j : ℝ) + 1) / K)
      g₁ hg₁c hab₁ hε
  -- ## the second piece
  have hV₂ : IsOpen {u : ℝ |
      γ u ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t ⟨j.1 + 1, hj'⟩))).source} :=
    ((chartAt (EuclideanSpace ℝ (Fin n)) (γ (t ⟨j.1 + 1, hj'⟩))).open_source.preimage hγ)
  have hf₂ : ContinuousOn (fun u : ℝ =>
      (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t ⟨j.1 + 1, hj'⟩))) (γ u))
      {u : ℝ | γ u ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t ⟨j.1 + 1, hj'⟩))).source} :=
    ((chartAt (EuclideanSpace ℝ (Fin n)) (γ (t ⟨j.1 + 1, hj'⟩)))).continuousOn.comp hγ.continuousOn
      (fun u hu => hu)
  obtain ⟨g₂, hg₂c, hg₂eq⟩ := exists_continuous_cutoff_extension _
    hV₂ isCompact_Icc (fun u hu => (hpiece ⟨j.1 + 1, hj'⟩ u hu).1) hf₂
  have hab₂ : ((⟨j.1 + 1, hj'⟩ : Fin K) : ℝ) / K ≤ (((⟨j.1 + 1, hj'⟩ : Fin K) : ℝ) + 1) / K :=
    div_le_div_of_nonneg_right (by linarith) (le_of_lt hKposR)
  obtain ⟨h₂, hh₂sm, hh₂a, _hh₂b, hh₂near⟩ :=
    exists_contDiff_near_fixing_ends (a := ((⟨j.1 + 1, hj'⟩ : Fin K) : ℝ) / K)
      (b := (((⟨j.1 + 1, hj'⟩ : Fin K) : ℝ) + 1) / K) g₂ hg₂c hab₂ hε
  -- ## assembly
  have hb₁mem : ((j : ℝ) + 1) / K ∈ Set.Icc ((j : ℝ) / K) (((j : ℝ) + 1) / K) :=
    Set.mem_Icc.mpr ⟨hab₁, le_refl _⟩
  have ha₂mem : (((⟨j.1 + 1, hj'⟩ : Fin K) : ℝ)) / K ∈
      Set.Icc (((⟨j.1 + 1, hj'⟩ : Fin K) : ℝ) / K)
        ((((⟨j.1 + 1, hj'⟩ : Fin K) : ℝ) + 1) / K) :=
    Set.mem_Icc.mpr ⟨le_refl _, hab₂⟩
  refine ⟨h₁, h₂, hh₁sm, hh₂sm, ?_, ?_, ?_, ?_⟩
  · rw [hh₁b, hg₁eq hb₁mem]
  · have h := hg₂eq ha₂mem
    rw [← hh₂a] at h
    rwa [hj'val] at h
  · intro s hs
    have hs' : g₁ s = (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))) (γ s) := hg₁eq hs
    rw [← hs']
    exact hh₁near s hs
  · intro s hs
    rw [hIcc] at hs
    have hs' : g₂ s
        = (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t ⟨j.1 + 1, hj'⟩))) (γ s) := hg₂eq hs
    rw [← hs']
    exact hh₂near s hs

/-! ## The whole chain, instantiated

The junction argument of `exists_junction_approximation`, applied once per piece: for every `ε > 0`
there is a family of `C^∞` maps `h j`, one per chain piece, each `ε`-close to the chartwise arc on
its piece and with **both** endpoints pinned to the chartwise values.  Consecutive pieces therefore
agree at their junction *through the chart transition*: at the junction `u* = (j+1)/K` one has

`h j u* = c_j (γ u*)`  and  `h (j+1) u* = c_{j+1} (γ u*) = (c_{j+1} ∘ c_j.symm) (h j u*)`,

the last identity being `c_j.left_inv` on the chart source.  No compatibility hypothesis is needed. -/
theorem exists_chain_approximation {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (γ : ℝ → M) (hγ : Continuous γ) {K : ℕ} (hK : 0 < K) {t ρ : Fin K → ℝ}
    (hpiece : ∀ j : Fin K, ∀ s ∈ Set.Icc ((j : ℝ) / K) (((j : ℝ) + 1) / K),
      γ s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))).source ∧
      (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))) (γ s) ∈
        Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))) (γ (t j))) (ρ j))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : Fin K → (ℝ → EuclideanSpace ℝ (Fin n)),
      (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (h j)) ∧
      (∀ j, h j ((j : ℝ) / K)
        = (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))) (γ ((j : ℝ) / K))) ∧
      (∀ j, h j (((j : ℝ) + 1) / K)
        = (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))) (γ (((j : ℝ) + 1) / K))) ∧
      (∀ j : Fin K, ∀ s ∈ Set.Icc ((j : ℝ) / K) (((j : ℝ) + 1) / K),
        ‖h j s - (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))) (γ s)‖ < ε) := by
  classical
  have hKposR : (0 : ℝ) < K := by exact_mod_cast hK
  have hstep : ∀ j : Fin K, ∃ h : ℝ → EuclideanSpace ℝ (Fin n),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h ∧
      h ((j : ℝ) / K) = (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))) (γ ((j : ℝ) / K)) ∧
      h (((j : ℝ) + 1) / K)
        = (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))) (γ (((j : ℝ) + 1) / K)) ∧
      (∀ s ∈ Set.Icc ((j : ℝ) / K) (((j : ℝ) + 1) / K),
        ‖h s - (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))) (γ s)‖ < ε) := by
    intro j
    have hV : IsOpen {u : ℝ | γ u ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))).source} :=
      ((chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))).open_source.preimage hγ)
    have hf : ContinuousOn (fun u : ℝ => (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))) (γ u))
        {u : ℝ | γ u ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))).source} :=
      ((chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j)))).continuousOn.comp hγ.continuousOn
        (fun u hu => hu)
    obtain ⟨g, hgc, hgeq⟩ := exists_continuous_cutoff_extension _
      hV isCompact_Icc (fun u hu => (hpiece j u hu).1) hf
    have hab : (j : ℝ) / K ≤ ((j : ℝ) + 1) / K :=
      div_le_div_of_nonneg_right (by linarith) (le_of_lt hKposR)
    obtain ⟨h, hsm, ha, hb, hnear⟩ :=
      exists_contDiff_near_fixing_ends (a := (j : ℝ) / K) (b := ((j : ℝ) + 1) / K)
        g hgc hab hε
    refine ⟨h, hsm, ?_, ?_, ?_⟩
    · rw [ha, hgeq (Set.mem_Icc.mpr ⟨le_refl _, hab⟩)]
    · rw [hb, hgeq (Set.mem_Icc.mpr ⟨hab, le_refl _⟩)]
    · intro s hs
      have hs' : g s = (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t j))) (γ s) := hgeq hs
      rw [← hs']
      exact hnear s hs
  choose h hsm ha hb hnear using hstep
  exact ⟨h, hsm, ha, hb, hnear⟩

/-- **Separated sets have disjoint thickenings.**  The *geometric core* of the per-junction
push: if the axis images of the two pieces are `δ`-separated (which
`Work.Whitney.tube_slab_thickening` gives for the two crossing pieces, whose axis images are disjoint
compact sub-arcs), then for a fibre radius `λ` with `2 * L * λ ≤ δ` the movable regions — the
`L * λ`-thickenings of the axes — are disjoint.  That is hypothesis `hdisj` of
`Work.Whitney.CutPush.slabPush_comp_on_inner`. -/
theorem disjoint_thickening_of_separated {F : Type*} [NormedAddCommGroup F]
    {X₁ X₂ : Set F} {δ r : ℝ} (hr : 0 < r) (hrδ : 2 * r ≤ δ)
    (hsep : ∀ x₁ ∈ X₁, ∀ x₂ ∈ X₂, δ ≤ ‖x₁ - x₂‖) :
    Disjoint (⋃ x ∈ X₁, Metric.ball x r) (⋃ x ∈ X₂, Metric.ball x r) := by
  rw [Set.disjoint_left]
  intro y hy₁ hy₂
  rcases Set.mem_iUnion.mp hy₁ with ⟨x₁, hx₁⟩
  rcases Set.mem_iUnion.mp hx₁ with ⟨hx₁X, hy₁b⟩
  rcases Set.mem_iUnion.mp hy₂ with ⟨x₂, hx₂⟩
  rcases Set.mem_iUnion.mp hx₂ with ⟨hx₂X, hy₂b⟩
  have h1 : dist y x₁ < r := Metric.mem_ball.mp hy₁b
  have h2 : dist y x₂ < r := Metric.mem_ball.mp hy₂b
  have h3 : δ ≤ dist x₁ x₂ := by rw [dist_eq_norm]; exact hsep x₁ hx₁X x₂ hx₂X
  have h4 : dist x₁ x₂ ≤ dist x₁ y + dist y x₂ := dist_triangle _ _ _
  have h5 : dist x₁ y = dist y x₁ := dist_comm _ _
  linarith

end Work.Whitney.CutPush
