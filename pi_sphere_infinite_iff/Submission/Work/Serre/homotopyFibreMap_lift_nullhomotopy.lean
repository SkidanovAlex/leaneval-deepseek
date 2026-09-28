import Mathlib
import Submission.Work.StemsB.exists_lift_rel
import Submission.Work.RatHurewicz.homotopyFibreMap_exists
import Submission.Work.Serre.C1Cyl

/-!
# Null-homotopies lift along the map of homotopy fibres of a pullback square

For a Serre fibration `q : E → B`, a map `g : C(Γ,B)` and the pullback square

  `Pullback q g --pullbackFst--> E`
  `     |                               |`
  `pullbackSnd                        q`
  `     v                               v`
  `     Γ ------- g ---------------> B`

the canonical map of homotopy fibres
`Φ = homotopyFibreMap (pullbackFst q g) g q (pullbackSnd q g) hsq x` sends a based `k`-cube `γ` of
`homotopyFibre (pullbackFst q g) x` to the based `k`-cube `(a,α) ↦ (pullbackSnd q g a, q ∘ α)` of
`homotopyFibre g (pullbackSnd q g x)`.  The main statement
`Work.Serre.homotopyFibreMap_lift_nullhomotopy` is that a null-homotopy of `Φ ∘ γ` *lifts* to a
null-homotopy of `γ`.

The proof is the standard lifting argument: the `B`-component of the null-homotopy, read as a
homotopy of `k`-cubes (`t ↦` the `t`-th point of the corresponding path of `B`), lifts along the
Serre fibration `q` with prescribed initial value `f x` and prescribed lateral boundary; the lift is
precisely the `E`-coordinate of the desired null-homotopy in the pullback.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre

open Work.StemsB

noncomputable section

variable {E B Γ : Type} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Γ]

theorem homotopyFibreMap_lift_nullhomotopy (q : C(E, B)) (g : C(Γ, B))
    (hq : IsSerreFibration q)
    (hsq : q.comp (pullbackFst q g) = g.comp (pullbackSnd q g))
    (x : Pullback q g) (k : ℕ)
    (γ : GenLoop (Fin k) (Work.RatHurewicz.homotopyFibre (pullbackFst q g) x)
      (Work.RatHurewicz.homotopyFibreBasepoint (pullbackFst q g) x))
    (hV : GenLoop.Homotopic
      (genLoopMap (Work.RatHurewicz.homotopyFibreMap (pullbackFst q g) g q (pullbackSnd q g) hsq x) k γ)
      (GenLoop.const : GenLoop (Fin k) (Work.RatHurewicz.homotopyFibre g (pullbackSnd q g x))
        (Work.RatHurewicz.homotopyFibreMap (pullbackFst q g) g q (pullbackSnd q g) hsq x
          (Work.RatHurewicz.homotopyFibreBasepoint (pullbackFst q g) x)))) :
    GenLoop.Homotopic γ (GenLoop.const : GenLoop (Fin k)
      (Work.RatHurewicz.homotopyFibre (pullbackFst q g) x)
      (Work.RatHurewicz.homotopyFibreBasepoint (pullbackFst q g) x)) := by
  classical
  obtain ⟨Hq⟩ := hV
  -- the pullback condition of the base point and of a general point of `F`
  have hx2 : q (pullbackFst q g x) = g (pullbackSnd q g x) := x.2
  have hγbp : ∀ {z : Fin k → I}, z ∈ Cube.boundary (Fin k) →
      (γ z).1.2.1 = ContinuousMap.const I (pullbackFst q g x) := by
    intro z hz
    exact (congrArg (fun y : Work.RatHurewicz.homotopyFibre (pullbackFst q g) x => y.1.2.1)
      (γ.2 z hz)).trans rfl
  -- *************** Step 0: the values of the null-homotopy ***************
  -- (`Φ` applied to a point of `F`; the `B`-path component)
  let pathG : C(Work.RatHurewicz.homotopyFibre g (pullbackSnd q g x), C(I, B)) :=
    ⟨fun y => y.1.2.1, continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)⟩
  let pathF : C(Work.RatHurewicz.homotopyFibre (pullbackFst q g) x, C(I, E)) :=
    ⟨fun y => y.1.2.1, continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)⟩
  let evB : C(C(I, B) × I, B) := ⟨fun z => z.1 z.2, continuous_eval⟩
  let evE : C(C(I, E) × I, E) := ⟨fun z => z.1 z.2, continuous_eval⟩
  -- the bridge `genLoopMap`-value
  have gbridge : ∀ z : Fin k → I,
      (genLoopMap (Work.RatHurewicz.homotopyFibreMap (pullbackFst q g) g q (pullbackSnd q g)
        hsq x) k γ) z
        = Work.RatHurewicz.homotopyFibreMap (pullbackFst q g) g q (pullbackSnd q g) hsq x
          (γ z) := fun z => rfl
  -- the constant cube
  have gconst : ∀ z : Fin k → I,
      (GenLoop.const : GenLoop (Fin k) (Work.RatHurewicz.homotopyFibre g (pullbackSnd q g x))
        (Work.RatHurewicz.homotopyFibreMap (pullbackFst q g) g q (pullbackSnd q g) hsq x
          (Work.RatHurewicz.homotopyFibreBasepoint (pullbackFst q g) x))) z
        = Work.RatHurewicz.homotopyFibreMap (pullbackFst q g) g q (pullbackSnd q g) hsq x
          (Work.RatHurewicz.homotopyFibreBasepoint (pullbackFst q g) x) := fun z => rfl
  -- the values of `Hq` at `s = 0`, at `s = 1` and on the lateral boundary
  have g0 : ∀ z : Fin k → I, Hq (0, z) = Work.RatHurewicz.homotopyFibreMap (pullbackFst q g) g q
      (pullbackSnd q g) hsq x (γ z) :=
    fun z => (Hq.apply_zero z).trans (gbridge z)
  have g1 : ∀ z : Fin k → I, Hq (1, z)
      = Work.RatHurewicz.homotopyFibreBasepoint g (pullbackSnd q g x) :=
    fun z => (Hq.apply_one z).trans ((gconst z).trans
      (Work.RatHurewicz.homotopyFibreMap_basepoint (pullbackFst q g) g q (pullbackSnd q g) hsq x))
  have gb : ∀ (s : I) {z : Fin k → I}, z ∈ Cube.boundary (Fin k) →
      Hq (s, z) = Work.RatHurewicz.homotopyFibreBasepoint g (pullbackSnd q g x) := by
    intro s z hz
    refine (by
      rw [Hq.eq_fst s hz]
      rfl : Hq (s, z) = Work.RatHurewicz.homotopyFibreMap (pullbackFst q g) g q (pullbackSnd q g)
        hsq x (γ z)).trans ?_
    exact ((congrArg (fun y => Work.RatHurewicz.homotopyFibreMap (pullbackFst q g) g q
        (pullbackSnd q g) hsq x y) (γ.2 z hz)).trans
      (Work.RatHurewicz.homotopyFibreMap_basepoint (pullbackFst q g) g q (pullbackSnd q g) hsq x))
  -- the Γ-coordinate of `Hq` at `s = 0`, `s = 1`, on the boundary
  have g0fst : ∀ z : Fin k → I, (Hq (0, z)).1.1 = ((γ z).1.1).1.2 := fun z =>
    (congrArg (fun y => y.1.1) (g0 z)).trans
      (Work.RatHurewicz.homotopyFibreMap_fst (pullbackFst q g) g q (pullbackSnd q g) hsq x (γ z))
  have g1fst : ∀ z : Fin k → I, (Hq (1, z)).1.1
      = (Work.RatHurewicz.homotopyFibreBasepoint g (pullbackSnd q g x)).1.1 :=
    fun z => congrArg (fun y => y.1.1) (g1 z)
  have gbfst : ∀ (s : I) {z : Fin k → I}, z ∈ Cube.boundary (Fin k) →
      (Hq (s, z)).1.1
        = (Work.RatHurewicz.homotopyFibreBasepoint g (pullbackSnd q g x)).1.1 :=
    fun s z hz => congrArg (fun y => y.1.1) (gb s hz)
  -- *************** Step 1: the homotopy to lift ***************
  let reindexCm : C((Fin (k+1) → I) × I, I × (Fin k → I)) :=
    ⟨fun z => (z.1 0, Fin.tail z.1), by
      apply Continuous.prodMk
      · exact (continuous_apply 0).comp continuous_fst
      · exact continuous_pi (fun i => (continuous_apply i.succ).comp continuous_fst)⟩
  let Hmap : C((Fin (k+1) → I) × I, B) :=
    evB.comp (((pathG.comp Hq.toContinuousMap).comp reindexCm).prodMk ContinuousMap.snd)
  have hHmap : ∀ (u : Fin (k+1) → I) (t : I),
      Hmap (u, t) = (Hq (u 0, Fin.tail u)).1.2.1 t := fun u t => rfl
  -- *************** Step 2: the prescribed data and the lift ***************
  let f₀ : C(Fin (k+1) → I, E) := ContinuousMap.const _ (pullbackFst q g x)
  have hf : q.comp f₀ = Hmap.comp (zeroIncl (k+1)) := by
    ext u
    show q (pullbackFst q g x) = Hmap (u, 0)
    rw [hHmap u 0]
    exact hx2.trans ((Hq (u 0, Fin.tail u)).1.2.2).symm
  let tailB : C(CubeBdry (k+1) × I, Fin k → I) :=
    ⟨fun z => Fin.tail z.1.1, by
      apply continuous_pi
      intro i
      exact (continuous_apply i.succ).comp (continuous_subtype_val.comp continuous_fst)⟩
  let sUCm : C(CubeBdry (k+1) × I, I) :=
    ⟨fun z => unitIntervalOneSub (z.1.1 0) * z.2, by
      exact ((continuous_unitIntervalOneSub.comp
        ((continuous_apply 0).comp (continuous_subtype_val.comp continuous_fst))).mul
          continuous_snd)⟩
  let g₀ : C(CubeBdry (k+1) × I, E) :=
    evE.comp ((pathF.comp (γ.1.comp tailB)).prodMk sUCm)
  have hg₀ : ∀ (u : Fin (k+1) → I) (hu : u ∈ Cube.boundary (Fin (k+1))) (t : I),
      g₀ (⟨u, hu⟩, t) = (γ (Fin.tail u)).1.2.1 (unitIntervalOneSub (u 0) * t) :=
    fun u hu t => rfl
  have hcons_zero_mem : ∀ z : Fin k → I, Fin.cons (0 : I) z ∈ Cube.boundary (Fin (k+1)) :=
    fun z => ⟨0, by rw [Fin.cons_zero]; exact Or.inl rfl⟩
  have hcons_one_mem : ∀ z : Fin k → I, Fin.cons (1 : I) z ∈ Cube.boundary (Fin (k+1)) :=
    fun z => ⟨0, by rw [Fin.cons_zero]; exact Or.inr rfl⟩
  have hcons_mem : ∀ (s : I) {z : Fin k → I}, z ∈ Cube.boundary (Fin k) →
      Fin.cons s z ∈ Cube.boundary (Fin (k+1)) := by
    intro s z hz
    obtain ⟨i, hi⟩ := hz
    exact ⟨i.succ, by simpa [Fin.cons_succ] using hi⟩
  have hg : q.comp g₀ = Hmap.comp (bdryIncl (k+1)) := by
    ext z
    rcases z with ⟨u, t⟩
    show q (g₀ (u, t)) = Hmap (u.1, t)
    rw [hg₀ u.1 u.2 t, hHmap u.1 t]
    rcases (Work.StemsB.mem_boundary_succ_iff k u.1).mp u.2 with (h | h) | h
    · -- `u.1 0 = 0`
      rw [h, unitIntervalOneSub_zero, one_mul]
      have h1 : (Hq (0, Fin.tail u.1)).1.2.1
          = (q.comp ((γ (Fin.tail u.1)).1.2.1) : C(I, B)) :=
        (congrArg (fun y => y.1.2.1) (g0 (Fin.tail u.1))).trans
          (Work.RatHurewicz.homotopyFibreMap_snd (pullbackFst q g) g q (pullbackSnd q g) hsq x
            (γ (Fin.tail u.1)))
      rw [h1] <;> rfl
    · -- `u.1 0 = 1`
      rw [h, unitIntervalOneSub_one, zero_mul]
      have h1 : (Hq (1, Fin.tail u.1)).1.2.1
          = (Work.RatHurewicz.homotopyFibreBasepoint g (pullbackSnd q g x)).1.2.1 :=
        congrArg (fun y => y.1.2.1) (g1 (Fin.tail u.1))
      have h2 : (Work.RatHurewicz.homotopyFibreBasepoint g (pullbackSnd q g x)).1.2.1
          = ContinuousMap.const I (g (pullbackSnd q g x)) := rfl
      have h3 : q ((γ (Fin.tail u.1)).1.2.1 0) = g (pullbackSnd q g x) :=
        (congrArg q ((γ (Fin.tail u.1)).1.2.2)).trans hx2
      rw [h3, h1, h2] <;> rfl
    · -- `Fin.tail u.1 ∈ Cube.boundary (Fin k)`
      have h1 : (Hq (u.1 0, Fin.tail u.1)).1.2.1
          = (Work.RatHurewicz.homotopyFibreBasepoint g (pullbackSnd q g x)).1.2.1 :=
        congrArg (fun y => y.1.2.1) (gb (u.1 0) h)
      have h2 : (Work.RatHurewicz.homotopyFibreBasepoint g (pullbackSnd q g x)).1.2.1
          = ContinuousMap.const I (g (pullbackSnd q g x)) := rfl
      have h3 : q ((γ (Fin.tail u.1)).1.2.1 (unitIntervalOneSub (u.1 0) * t))
          = g (pullbackSnd q g x) := by
        rw [hγbp h]
        simpa using hx2
      rw [h3, h1, h2] <;> rfl
  have hg0 : ∀ u : CubeBdry (k+1), g₀ (u, 0) = f₀ u.1 := by
    intro u
    rw [hg₀ u.1 u.2 0]
    show (γ (Fin.tail u.1)).1.2.1 (unitIntervalOneSub (u.1 0) * 0) = pullbackFst q g x
    rw [mul_zero, (γ (Fin.tail u.1)).1.2.2] <;> rfl
  obtain ⟨G, hGq, hG0, hGbd⟩ := exists_lift_rel q hq (k+1) Hmap f₀ hf g₀ hg hg0
  -- *************** Step 3: the `F`-valued homotopy ***************
  let consCm : C(I × (Fin k → I), Fin (k+1) → I) :=
    ⟨fun z => Fin.cons z.1 z.2, Continuous.finCons continuous_fst continuous_snd⟩
  let HqFst : C(I × (Fin k → I), Γ) :=
    (Work.RatHurewicz.homotopyFibreFst g (pullbackSnd q g x)).comp Hq.toContinuousMap
  let Glast : C(I × (Fin k → I), E) :=
    G.comp (consCm.prodMk (ContinuousMap.const (I × (Fin k → I)) (1 : I)))
  let Pcurry : C(I × (Fin k → I), C(I, E)) :=
    (G.comp ((consCm.comp ContinuousMap.fst).prodMk ContinuousMap.snd)).curry
  have hGlast : ∀ z : I × (Fin k → I), Glast z = G (Fin.cons z.1 z.2, 1) := fun z => rfl
  have hPcurry : ∀ (z : I × (Fin k → I)) (t : I), Pcurry z t = G (Fin.cons z.1 z.2, t) :=
    fun z t => rfl
  have hHqFst : ∀ z : I × (Fin k → I), HqFst z = (Hq (z.1, z.2)).1.1 := fun z => rfl
  have hXmem : ∀ z : I × (Fin k → I), q (Glast z) = g (HqFst z) := by
    intro z
    rw [hGlast, hHqFst]
    have h1 : q (G (Fin.cons z.1 z.2, 1)) = Hmap (Fin.cons z.1 z.2, 1) := by
      have h := congrFun (congrArg DFunLike.coe hGq) (Fin.cons z.1 z.2, 1)
      simpa using h
    rw [h1, hHmap (Fin.cons z.1 z.2) 1, Fin.cons_zero, Fin.tail_cons]
    exact (Hq (z.1, z.2)).2
  have hmemb : ∀ z : I × (Fin k → I), Pcurry z 0 = pullbackFst q g x := by
    intro z
    rw [hPcurry, hG0 (Fin.cons z.1 z.2)]
    rfl
  have hmemb' : ∀ z : I × (Fin k → I),
      evalOne E (pullbackFst q g x) ⟨Pcurry z, hmemb z⟩
        = pullbackFst q g (⟨(Glast z, HqFst z), hXmem z⟩ : Pullback q g) := by
    intro z
    show Pcurry z 1 = Glast z
    rw [hPcurry, hGlast] <;> rfl
  let UU : C(I × (Fin k → I), Work.RatHurewicz.homotopyFibre (pullbackFst q g) x) :=
    ⟨fun z => ⟨(⟨(Glast z, HqFst z), hXmem z⟩, ⟨Pcurry z, hmemb z⟩), hmemb' z⟩, by
      refine Continuous.subtype_mk ?_ _
      refine Continuous.prodMk ?_ ?_
      · refine Continuous.subtype_mk ?_ _
        exact Continuous.prodMk Glast.continuous HqFst.continuous
      · exact Continuous.subtype_mk Pcurry.continuous hmemb⟩
  have hUU : ∀ z : I × (Fin k → I),
      UU z = (⟨(⟨(Glast z, HqFst z), hXmem z⟩, ⟨Pcurry z, hmemb z⟩), hmemb' z⟩
        : Work.RatHurewicz.homotopyFibre (pullbackFst q g) x) := fun z => rfl
  -- *************** Step 4: the computations at the three kinds of boundary ***************
  have hγ2 : ∀ z : Fin k → I, (γ z).1.2.1 1 = pullbackFst q g ((γ z).1.1) := fun z => (γ z).2
  have hGlast0 : ∀ z : Fin k → I, Glast (0, z) = (γ z).1.1.1.1 := by
    intro z
    have h1 : Glast (0, z) = (γ z).1.2.1 (unitIntervalOneSub (0 : I) * (1 : I)) := by
      rw [hGlast, hGbd ⟨Fin.cons 0 z, hcons_zero_mem z⟩ 1,
        hg₀ (Fin.cons 0 z) (hcons_zero_mem z) 1]
      simp only [Fin.cons_zero, Fin.tail_cons]
    rw [h1, unitIntervalOneSub_zero, one_mul, hγ2 z] <;> rfl
  have hHqFst0 : ∀ z : Fin k → I, HqFst (0, z) = (γ z).1.1.1.2 := by
    intro z
    rw [hHqFst]
    exact (g0fst z).trans rfl
  have hPcurry0 : ∀ (z : Fin k → I) (t : I), Pcurry (0, z) t = (γ z).1.2.1 t := by
    intro z t
    have h1 : Pcurry (0, z) t = (γ z).1.2.1 (unitIntervalOneSub (0 : I) * t) := by
      rw [hPcurry, hGbd ⟨Fin.cons 0 z, hcons_zero_mem z⟩ t,
        hg₀ (Fin.cons 0 z) (hcons_zero_mem z) t]
      simp only [Fin.cons_zero, Fin.tail_cons]
    rw [h1, unitIntervalOneSub_zero, one_mul] <;> rfl
  have hGlast1 : ∀ z : Fin k → I, Glast (1, z) = (pullbackFst q g x) := by
    intro z
    have h1 : Glast (1, z) = (γ z).1.2.1 (unitIntervalOneSub (1 : I) * (1 : I)) := by
      rw [hGlast, hGbd ⟨Fin.cons 1 z, hcons_one_mem z⟩ 1,
        hg₀ (Fin.cons 1 z) (hcons_one_mem z) 1]
      simp only [Fin.cons_zero, Fin.tail_cons]
    rw [h1, unitIntervalOneSub_one, zero_mul, (γ z).1.2.2] <;> rfl
  have hHqFst1 : ∀ z : Fin k → I, HqFst (1, z) = pullbackSnd q g x := by
    intro z
    rw [hHqFst]
    exact (g1fst z).trans rfl
  have hPcurry1 : ∀ (z : Fin k → I) (t : I), Pcurry (1, z) t = pullbackFst q g x := by
    intro z t
    have h1 : Pcurry (1, z) t = (γ z).1.2.1 (unitIntervalOneSub (1 : I) * t) := by
      rw [hPcurry, hGbd ⟨Fin.cons 1 z, hcons_one_mem z⟩ t,
        hg₀ (Fin.cons 1 z) (hcons_one_mem z) t]
      simp only [Fin.cons_zero, Fin.tail_cons]
    rw [h1, unitIntervalOneSub_one, zero_mul, (γ z).1.2.2] <;> rfl
  have hGlastB : ∀ (s : I) {z : Fin k → I}, z ∈ Cube.boundary (Fin k) →
      Glast (s, z) = pullbackFst q g x := by
    intro s z hz
    have h1 : Glast (s, z) = (γ z).1.2.1 (unitIntervalOneSub s * (1 : I)) := by
      rw [hGlast, hGbd ⟨Fin.cons s z, hcons_mem s hz⟩ 1,
        hg₀ (Fin.cons s z) (hcons_mem s hz) 1]
      simp only [Fin.cons_zero, Fin.tail_cons]
    rw [h1, hγbp hz] <;> rfl
  have hHqFstB : ∀ (s : I) {z : Fin k → I}, z ∈ Cube.boundary (Fin k) →
      HqFst (s, z) = pullbackSnd q g x := by
    intro s z hz
    rw [hHqFst]
    exact (gbfst s hz).trans rfl
  have hPcurryB : ∀ (s : I) {z : Fin k → I}, z ∈ Cube.boundary (Fin k) → ∀ t : I,
      Pcurry (s, z) t = pullbackFst q g x := by
    intro s z hz t
    have h1 : Pcurry (s, z) t = (γ z).1.2.1 (unitIntervalOneSub s * t) := by
      rw [hPcurry, hGbd ⟨Fin.cons s z, hcons_mem s hz⟩ t,
        hg₀ (Fin.cons s z) (hcons_mem s hz) t]
      simp only [Fin.cons_zero, Fin.tail_cons]
    rw [h1, hγbp hz] <;> rfl
  -- the same, in the form adapted to `γ z` (for `z` on the boundary)
  have hBγ : ∀ {z : Fin k → I}, z ∈ Cube.boundary (Fin k) →
      (γ z).1.1 = x := by
    intro z hz
    exact congrArg (fun y : Work.RatHurewicz.homotopyFibre (pullbackFst q g) x => y.1.1)
      (γ.2 z hz)
  have hGlastB' : ∀ (s : I) {z : Fin k → I}, z ∈ Cube.boundary (Fin k) →
      Glast (s, z) = (γ z).1.1.1.1 := by
    intro s z hz
    exact (hGlastB s hz).trans (congrArg (fun y : Pullback q g => y.1.1) (hBγ hz)).symm
  have hHqFstB' : ∀ (s : I) {z : Fin k → I}, z ∈ Cube.boundary (Fin k) →
      HqFst (s, z) = (γ z).1.1.1.2 := by
    intro s z hz
    exact (hHqFstB s hz).trans (congrArg (fun y : Pullback q g => y.1.2) (hBγ hz)).symm
  have hPcurryB' : ∀ (s : I) {z : Fin k → I}, z ∈ Cube.boundary (Fin k) → ∀ t : I,
      Pcurry (s, z) t = (γ z).1.2.1 t := by
    intro s z hz t
    have h2 : (γ z).1.2.1 t = pullbackFst q g x :=
      (congrArg (fun p : C(I, E) => p t) (hγbp hz)).trans
        (rfl : (ContinuousMap.const I (pullbackFst q g x)) t = pullbackFst q g x)
    exact (hPcurryB s hz t).trans h2.symm
  -- the constant cube of `F`
  have hconstF : ∀ z : Fin k → I,
      (GenLoop.const : GenLoop (Fin k) (Work.RatHurewicz.homotopyFibre (pullbackFst q g) x)
        (Work.RatHurewicz.homotopyFibreBasepoint (pullbackFst q g) x)) z
        = Work.RatHurewicz.homotopyFibreBasepoint (pullbackFst q g) x := fun z => rfl
  -- comparing two points of `F` componentwise
  have key : ∀ (z : I × (Fin k → I)) (y : Work.RatHurewicz.homotopyFibre (pullbackFst q g) x),
      Glast z = y.1.1.1.1 → HqFst z = y.1.1.1.2 → (∀ t : I, Pcurry z t = y.1.2.1 t) →
      UU z = y := by
    intro z y h1 h2 h3
    rw [hUU]
    refine Subtype.ext ?_
    refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      exact Prod.ext h1 h2
    · refine Subtype.ext ?_
      ext t
      exact h3 t
  have hhom : (γ.1 : C(Fin k → I, Work.RatHurewicz.homotopyFibre (pullbackFst q g) x)).HomotopyRel
      ((GenLoop.const : GenLoop (Fin k)
        (Work.RatHurewicz.homotopyFibre (pullbackFst q g) x)
        (Work.RatHurewicz.homotopyFibreBasepoint (pullbackFst q g) x)).1)
      (Cube.boundary (Fin k)) :=
    { toFun := ⇑UU, continuous_toFun := UU.continuous
      map_zero_left := fun z => key (0, z) (γ z) (hGlast0 z) (hHqFst0 z) (hPcurry0 z)
      map_one_left := fun z => key (1, z) (Work.RatHurewicz.homotopyFibreBasepoint
        (pullbackFst q g) x) (hGlast1 z) (hHqFst1 z) (hPcurry1 z)
      prop' := fun s z hz => key (s, z) (γ z) (hGlastB' s hz) (hHqFstB' s hz) (hPcurryB' s hz) }
  exact ⟨hhom⟩

end

end Work.Serre
