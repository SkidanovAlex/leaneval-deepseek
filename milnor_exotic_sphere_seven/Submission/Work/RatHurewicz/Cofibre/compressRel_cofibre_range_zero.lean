import Mathlib
import Submission.Work.RatHurewicz.Cofibre.Basic
import Submission.Work.RatHurewicz.Cofibre.Cover
import Submission.Work.RatHurewicz.Cofibre.UShrink
import Submission.Work.RatHurewicz.Cofibre.VContract
import Submission.Work.RatHurewicz.Cofibre.collarHomotopyEquiv
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.RatHurewicz.compression_of_relPiVanishing
import Submission.Work.Serre.homotopyFibre_pathConnected
import Submission.Work.Serre.pathConnectedSpace_homotopyFibre
import Submission.Work.RatHurewicz.ConnectivityBridge
import Submission.Work.RatHurewicz.SimplyConnectedBridge
import Submission.Work.Stems.subsingleton_of_contraction
import Submission.Work.RatHurewicz.Cofibre.path_compress_twoSet

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option linter.unusedVariables false

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {E F : Type} [TopologicalSpace E] [TopologicalSpace F]

/-! ## Preliminary general lemmas about paths -/

/-- **Path connectedness transfers along a homotopy equivalence.** -/
theorem nonempty_path_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (hY : ∀ a b : Y, Nonempty (Path a b)) :
    ∀ a b : X, Nonempty (Path a b) := by
  intro a b
  obtain ⟨γ⟩ := hY (e.toFun a) (e.toFun b)
  obtain ⟨H⟩ := e.left_inv
  have hA : Path (e.invFun (e.toFun a)) a :=
    ⟨⟨fun t => H (t, a), H.continuous.comp (continuous_id.prodMk continuous_const)⟩,
      H.map_zero_left a, H.map_one_left a⟩
  have hB : Path (e.invFun (e.toFun b)) b :=
    ⟨⟨fun t => H (t, b), H.continuous.comp (continuous_id.prodMk continuous_const)⟩,
      H.map_zero_left b, H.map_one_left b⟩
  exact ⟨hA.symm.trans ((γ.map (f := ⇑e.invFun) e.invFun.continuous).trans hB)⟩

/-- **In a contractible space any two paths with the same endpoints are homotopic.** -/
theorem homotopic_of_contraction {X : Type} [TopologicalSpace X] (b : X)
    (H : C(X × unitInterval, X)) (h0 : ∀ x, H (x, 0) = x) (h1 : ∀ x, H (x, 1) = b)
    {x y : X} (p q : Path x y) : Nonempty (Path.Homotopic p q) := by
  haveI : Subsingleton (HomotopyGroup (Fin 0) X x) :=
    Work.Stems.subsingleton_of_contraction b H h0 h1 0 x
  haveI : Subsingleton (HomotopyGroup (Fin 1) X x) :=
    Work.Stems.subsingleton_of_contraction b H h0 h1 1 x
  haveI : SimplyConnectedSpace X :=
    simplyConnectedSpace_of_subsingleton x inferInstance inferInstance
  have hq : Subsingleton (Path.Homotopic.Quotient x y) :=
    (simply_connected_iff_paths_homotopic.mp inferInstance).2 x y
  exact ⟨Path.Homotopic.Quotient.eq.mp (hq.elim _ _)⟩

/-- The path in the subtype `↥A` obtained by promoting a path of `X` with values in `A`. -/
def pathOfMem {X : Type} [TopologicalSpace X] {A : Set X} {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (p : Path x y) (hp : ∀ t, p t ∈ A) : Path (X := ↥A) ⟨x, hx⟩ ⟨y, hy⟩ where
  toContinuousMap :=
    ⟨fun t => ⟨p t, hp t⟩,
      Continuous.subtype_mk (f := fun t : unitInterval => p t) p.continuous hp⟩
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

theorem pathOfMem_map_val {X : Type} [TopologicalSpace X] {A : Set X} {x y : X} (hx : x ∈ A)
    (hy : y ∈ A) (p : Path x y) (hp : ∀ t, p t ∈ A) :
    (pathOfMem hx hy p hp).map (f := Subtype.val) continuous_subtype_val = p := by
  apply Path.ext
  funext t
  rfl

theorem setInclPath_pathOfMem {X : Type} [TopologicalSpace X] {A : Set X} {x y : X} (hx : x ∈ A)
    (hy : y ∈ A) (p : Path x y) (hp : ∀ t, p t ∈ A) :
    setInclPath ⟨x, hx⟩ ⟨y, hy⟩ (pathOfMem hx hy p hp) = p := by
  apply Path.ext
  funext t
  rw [setInclPath_apply]
  rfl

/-! ## Path connectedness of the homotopy fibre from the path-compression property -/

/-- **The homotopy fibre of `A ↪ X` at `a₀` is path connected** if every path of `X` with endpoints
in `A` is homotopic, relative to its endpoints, to a path with values in `A`. -/
theorem pathConnectedSpace_homotopyFibre_of_pathCompress {X : Type} [TopologicalSpace X] {A : Set X}
    (hcomp : ∀ {x y : X} (hx : x ∈ A) (hy : y ∈ A) (p : Path x y),
      ∃ q : Path x y, (∀ t, q t ∈ A) ∧ Nonempty (Path.Homotopic p q))
    (a₀ : ↥A) : PathConnectedSpace (homotopyFibre (setIncl A) a₀) := by
  refine ⟨⟨homotopyFibreBasepoint (setIncl A) a₀⟩, fun p q => ?_⟩
  have key : ∀ p : homotopyFibre (setIncl A) a₀,
      Joined (homotopyFibreBasepoint (setIncl A) a₀) p := by
    intro p
    obtain ⟨δ, hδA, hhom⟩ := hcomp a₀.2 p.1.1.2 (fibrePath p)
    obtain ⟨hhom'⟩ := hhom
    have h1 : Joined (fibrePoint (fibrePath p)) (fibrePoint δ) :=
      joined_fibrePoint_of_homotopic hhom'
    have h2 : Joined (homotopyFibreBasepoint (setIncl A) a₀) (fibrePoint δ) := by
      have h3 := joined_basepoint_fibrePoint a₀ (p.1.1) (pathOfMem a₀.2 (p.1.1).2 δ hδA)
      rw [show setInclPath a₀ (p.1.1) (pathOfMem a₀.2 (p.1.1).2 δ hδA) = δ from
        setInclPath_pathOfMem a₀.2 (p.1.1).2 δ hδA] at h3
      exact h3
    rw [Work.Serre.fibrePoint_fibrePath p] at h1
    exact h2.trans h1.symm
  exact (key p).symm.trans (key q)

/-- **The `π₀` of the homotopy fibre vanishes** under the path-compression hypothesis. -/
theorem subsingleton_relPi_zero_of_pathCompress {X : Type} [TopologicalSpace X] {A : Set X}
    (hcomp : ∀ {x y : X} (hx : x ∈ A) (hy : y ∈ A) (p : Path x y),
      ∃ q : Path x y, (∀ t, q t ∈ A) ∧ Nonempty (Path.Homotopic p q))
    (a₀ : ↥A) : Subsingleton (RelHomotopyGroup (setIncl A) a₀ 0) := by
  have hpc := pathConnectedSpace_homotopyFibre_of_pathCompress hcomp a₀
  have hZ : Subsingleton (ZerothHomotopy (homotopyFibre (setIncl A) a₀)) :=
    (pathConnectedSpace_iff_zerothHomotopy.mp hpc).2
  exact ⟨fun x y => (HomotopyGroup.pi0EquivZerothHomotopy
    (x := homotopyFibreBasepoint (setIncl A) a₀)).injective (hZ.elim _ _)⟩

/-! ## The cofibre of `ι` -/

/-- The retraction of the half-open cone fixes the image of `E`. -/
theorem cofibreURetract_cofibreUIncl (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E) (e : E) :
    cofibreURetract ι e₀ (cofibreUIncl ι e) = e :=
  congrFun (congrArg (fun k : C(E, E) => ⇑k) (cofibreURetract_comp_cofibreUIncl ι e₀)) e

/-- The shrink homotopy of the half-open cone fixes the image of `E` (the "`A`" of the pair). -/
theorem uShrink_cofibreUIncl (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E) (e : E)
    (s : unitInterval) : uShrink ι e₀ (cofibreUIncl ι e, s) = cofibreUIncl ι e := by
  have hmem : (Sum.inl e : E ⊕ Work.Stems.Cone F) ∈
      (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreU ι :=
    cofibreIncl_mem_cofibreU ι e
  have hpt : cofibreUIncl ι e = cofibreUQuot ι ⟨Sum.inl e, hmem⟩ := Subtype.ext rfl
  rw [hpt, uShrink_apply, uShrinkQuot_eq ι e₀ ⟨Sum.inl e, hmem⟩, uShrinkRaw_apply]
  refine Subtype.ext ?_
  show ((uShrinkFun ι e₀ (Sum.inl e)) s : cofibre ι) = cofibreIncl ι e
  rw [uShrinkFun_inl, uShrinkF_apply]

/-- **`cofibreU ι ∩ cofibreV ι` is path connected** when `F` is. -/
theorem nonempty_path_cofibre_inter (ι : C(F, E)) [Nonempty F]
    (hF : ∀ a b : F, Nonempty (Path a b)) :
    ∀ a b : ↥(cofibreU ι ∩ cofibreV ι), Nonempty (Path a b) := by
  obtain ⟨e⟩ := Cofibre.collarHomotopyEquiv ι
  exact nonempty_path_of_homotopyEquiv e hF

/-- **Paths of the cofibre with values in `cofibreV ι` are homotopic** (when `F` is nonempty):
`cofibreV ι` is contractible. -/
theorem homotopic_of_mem_cofibreV (ι : C(F, E)) [Nonempty F] {x y : cofibre ι} (p q : Path x y)
    (hp : ∀ t, p t ∈ cofibreV ι) (hq : ∀ t, q t ∈ cofibreV ι) :
    Nonempty (Path.Homotopic p q) := by
  obtain ⟨H, h0, b, h1⟩ := exists_contraction_cofibreV ι
  have hx : x ∈ cofibreV ι := p.source ▸ hp 0
  have hy : y ∈ cofibreV ι := p.target ▸ hp 1
  let f : C(↥(cofibreV ι), cofibre ι) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨h'⟩ := homotopic_of_contraction b H h0 h1
    (pathOfMem hx hy p hp) (pathOfMem hx hy q hq)
  have hmap := Path.Homotopic.map h' f
  rw [show (pathOfMem hx hy p hp).map (f := ⇑f) f.continuous
        = (pathOfMem hx hy p hp).map (f := Subtype.val) continuous_subtype_val from rfl,
      show (pathOfMem hx hy q hq).map (f := ⇑f) f.continuous
        = (pathOfMem hx hy q hq).map (f := Subtype.val) continuous_subtype_val from rfl,
      pathOfMem_map_val hx hy p hp, pathOfMem_map_val hx hy q hq] at hmap
  exact ⟨hmap⟩

/-- **The path compression of the pair `(cofibre ι, range (cofibreIncl ι))`.** -/
theorem path_compress_range (ι : C(F, E)) (y₀ : F)
    (hF0 : Subsingleton (HomotopyGroup (Fin 0) F y₀)) :
    ∀ (x y : cofibre ι), x ∈ Set.range ⇑(cofibreIncl ι) →
      y ∈ Set.range ⇑(cofibreIncl ι) → (p : Path x y) →
      ∃ q : Path x y, (∀ t, q t ∈ Set.range ⇑(cofibreIncl ι)) ∧
        Nonempty (Path.Homotopic p q) := by
  haveI : Nonempty F := ⟨y₀⟩
  haveI : Nonempty E := ⟨ι y₀⟩
  have hFpc : ∀ a b : F, Nonempty (Path a b) := by
    haveI : PathConnectedSpace F := pathConnectedSpace_of_subsingleton_pi_zero y₀ hF0
    intro a b
    exact PathConnectedSpace.joined a b
  have memU : ∀ {z : cofibre ι}, z ∈ Set.range ⇑(cofibreIncl ι) → z ∈ cofibreU ι := by
    rintro z ⟨e, rfl⟩
    exact cofibreIncl_mem_cofibreU ι e
  intro x y hx hy p
  obtain ⟨q₁, hq₁, hhom₁⟩ := Cofibre.path_compress_twoSet (isOpen_cofibreU ι) (isOpen_cofibreV ι)
    (cofibreU_union_cofibreV ι) (nonempty_path_cofibre_inter ι hFpc)
    (homotopic_of_mem_cofibreV ι) (memU hx) (memU hy) p
  obtain ⟨ex, hex⟩ := hx
  obtain ⟨ey, hey⟩ := hy
  -- the pushed path
  have hsubx : (⟨q₁ 0, hq₁ 0⟩ : ↥(cofibreU ι)) = cofibreUIncl ι ex := by
    apply Subtype.ext
    show q₁ 0 = ↑(cofibreUIncl ι ex)
    rw [q₁.source, cofibreUIncl_apply]
    exact hex.symm
  have hsuby : (⟨q₁ 1, hq₁ 1⟩ : ↥(cofibreU ι)) = cofibreUIncl ι ey := by
    apply Subtype.ext
    show q₁ 1 = ↑(cofibreUIncl ι ey)
    rw [q₁.target, cofibreUIncl_apply]
    exact hey.symm
  have hq₂A : ∀ t, (↑(cofibreUIncl ι (cofibreURetract ι (ι y₀) ⟨q₁ t, hq₁ t⟩)) : cofibre ι)
      ∈ Set.range ⇑(cofibreIncl ι) :=
    fun t => ⟨cofibreURetract ι (ι y₀) ⟨q₁ t, hq₁ t⟩, by rw [cofibreUIncl_apply]⟩
  have hq₂src : (↑(cofibreUIncl ι (cofibreURetract ι (ι y₀) ⟨q₁ 0, hq₁ 0⟩)) : cofibre ι) = x := by
    rw [hsubx, cofibreURetract_cofibreUIncl ι (ι y₀) ex, cofibreUIncl_apply]
    exact hex
  have hq₂tgt : (↑(cofibreUIncl ι (cofibreURetract ι (ι y₀) ⟨q₁ 1, hq₁ 1⟩)) : cofibre ι) = y := by
    rw [hsuby, cofibreURetract_cofibreUIncl ι (ι y₀) ey, cofibreUIncl_apply]
    exact hey
  let q₂ : Path x y :=
    ⟨⟨fun t => ↑(cofibreUIncl ι (cofibreURetract ι (ι y₀) ⟨q₁ t, hq₁ t⟩)),
        (continuous_subtype_val.comp (cofibreUIncl ι).continuous).comp
          ((cofibreURetract ι (ι y₀)).continuous.comp
            (Continuous.subtype_mk (f := fun t : unitInterval => q₁ t) q₁.continuous hq₁))⟩,
      hq₂src, hq₂tgt⟩
  -- the homotopy `q₁ ~ q₂` given by the shrink homotopy
  have hhom₂ : Nonempty (Path.Homotopic q₁ q₂) := by
    refine ⟨⟨⟨⟨fun st : unitInterval × unitInterval =>
                  ↑(uShrink ι (ι y₀) (⟨q₁ st.2, hq₁ st.2⟩, st.1)), ?_⟩, ?_, ?_⟩, ?_⟩⟩
    · exact (continuous_subtype_val.comp (uShrink ι (ι y₀)).continuous).comp
        ((Continuous.subtype_mk (f := fun st : unitInterval × unitInterval => q₁ st.2)
            (q₁.continuous.comp continuous_snd) (fun st => hq₁ st.2)).prodMk continuous_fst)
    · intro t
      show (↑(uShrink ι (ι y₀) (⟨q₁ t, hq₁ t⟩, 0)) : cofibre ι) = q₁ t
      rw [uShrink_zero]
    · intro t
      show (↑(uShrink ι (ι y₀) (⟨q₁ t, hq₁ t⟩, 1)) : cofibre ι) = q₂ t
      rw [uShrink_one]
      rfl
    · intro t s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with hs | hs
      · subst hs
        show (↑(uShrink ι (ι y₀) (⟨q₁ 0, hq₁ 0⟩, t)) : cofibre ι) = q₁ 0
        rw [hsubx, uShrink_cofibreUIncl, cofibreUIncl_apply]
        exact hex.trans q₁.source.symm
      · subst hs
        show (↑(uShrink ι (ι y₀) (⟨q₁ 1, hq₁ 1⟩, t)) : cofibre ι) = q₁ 1
        rw [hsuby, uShrink_cofibreUIncl, cofibreUIncl_apply]
        exact hey.trans q₁.target.symm
  obtain ⟨hhom₁'⟩ := hhom₁
  obtain ⟨hhom₂'⟩ := hhom₂
  exact ⟨q₂, hq₂A, ⟨hhom₁'.trans hhom₂'⟩⟩

/-- The path in the cone that lowers the height to `0`: `s ↦ [q.1, (1-s)·q.2]`. -/
def coneDownFun (q : F × unitInterval) : C(unitInterval, Work.Stems.Cone F) where
  toFun s := Quotient.mk'' (q.1, shrinkPt s q.2)
  continuous_toFun :=
    continuous_quotient_mk'.comp (Continuous.prodMk continuous_const
      (shrinkPtC.continuous.comp (Continuous.prodMk continuous_id continuous_const)))

/-- **Every point of the cofibre is joined to the image of `E`.** -/
theorem exists_path_to_range (ι : C(F, E)) (y : cofibre ι) :
    ∃ a : ↥(Set.range ⇑(cofibreIncl ι)), Nonempty (Path y a) := by
  obtain ⟨w, rfl⟩ := Quotient.exists_rep y
  rcases w with x | z
  · exact ⟨⟨cofibreIncl ι x, ⟨x, rfl⟩⟩, ⟨Path.refl _⟩⟩
  · obtain ⟨q, rfl⟩ := Quotient.exists_rep z
    refine ⟨⟨cofibreIncl ι (ι q.1), ⟨ι q.1, rfl⟩⟩, ⟨?_⟩⟩
    refine Path.mk ((cofibreInclCone ι).comp (coneDownFun q)) ?_ ?_
    · show cofibreInclCone ι (coneDownFun q 0) = Quotient.mk'' (Sum.inr (Quotient.mk'' q))
      rw [show coneDownFun q 0 = Quotient.mk'' q from by
        show Quotient.mk'' (q.1, shrinkPt 0 q.2) = Quotient.mk'' q
        rw [shrinkPt_zero]]
      rfl
    · show cofibreInclCone ι (coneDownFun q 1) = cofibreIncl ι (ι q.1)
      rw [show coneDownFun q 1 = Work.Stems.coneIncl q.1 from by
        show Quotient.mk'' (q.1, shrinkPt 1 q.2) = Work.Stems.coneIncl q.1
        rw [shrinkPt_one]
        rfl]
      exact (cofibreIncl_coneIncl ι q.1).symm

end

namespace Cofibre

/-- **The `n = 0` case of `Cofibre.compressRel_cofibre_range`**: for any `ι : C(F, E)` with `F` path connected (`π₀(F) = 0`), the pair `(cofibre ι, range (cofibreIncl ι))` compresses in dimensions `0` and `1`. In dimension `1` this says that every path in the cofibre `E ∪_F CF` with both endpoints in the image of `E` is homotopic relative to its endpoints into the image of `E`, i.e. `π₁(E) → π₁(E ∪_F CF)` is surjective (van Kampen: `π₁(E ∪_F CF)` is the quotient of `π₁(E)` by the normal closure of the image of `π₁(F)`). -/
theorem compressRel_cofibre_range_zero {E F : Type} [TopologicalSpace E] [TopologicalSpace F]
    (ι : C(F, E)) (y₀ : F)
    (hF0 : Subsingleton (HomotopyGroup (Fin 0) F y₀)) :
    ∀ d, d ≤ 1 → Work.RatHurewicz.CompressRel (Work.RatHurewicz.cofibre ι)
      (Set.range ⇑(Work.RatHurewicz.cofibreIncl ι)) d := by
  have hcomp : ∀ {x y : Work.RatHurewicz.cofibre ι},
      x ∈ Set.range ⇑(Work.RatHurewicz.cofibreIncl ι) →
      y ∈ Set.range ⇑(Work.RatHurewicz.cofibreIncl ι) → (p : Path x y) →
      ∃ q : Path x y, (∀ t, q t ∈ Set.range ⇑(Work.RatHurewicz.cofibreIncl ι)) ∧
        Nonempty (Path.Homotopic p q) :=
    fun {x y} hx hy p => Work.RatHurewicz.path_compress_range ι y₀ hF0 x y hx hy p
  have hconn : ∀ y : Work.RatHurewicz.cofibre ι,
      ∃ a : ↥(Set.range ⇑(Work.RatHurewicz.cofibreIncl ι)),
        Nonempty (Path y a) :=
    fun y => Work.RatHurewicz.exists_path_to_range ι y
  have hvan : ∀ a : ↥(Set.range ⇑(Work.RatHurewicz.cofibreIncl ι)), ∀ k, k ≤ 0 →
      Subsingleton (Work.RatHurewicz.RelHomotopyGroup
        (Work.RatHurewicz.setIncl (Set.range ⇑(Work.RatHurewicz.cofibreIncl ι))) a k) := by
    intro a k hk
    obtain rfl : k = 0 := by omega
    exact Work.RatHurewicz.subsingleton_relPi_zero_of_pathCompress hcomp a
  intro d hd
  exact Work.RatHurewicz.compression_of_relPiVanishing 0 hconn hvan d (by omega)

end Cofibre

end Work.RatHurewicz
