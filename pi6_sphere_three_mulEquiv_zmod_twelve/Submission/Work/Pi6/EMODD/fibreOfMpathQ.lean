import Mathlib
import Submission.Work.Pi6.EMODD.Defs
import Submission.Work.Serre.mpathQ_isSerreFibration
import Submission.Work.Serre.mpathQ_fibreHomeo
import Submission.Work.FGThm.mpathHomotopyEquiv
import Submission.Work.StemsB.fibrationLES_of_serre
import Submission.Work.Serre.subsingleton_pi0_homotopyFibre
import Submission.Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration
import Submission.Work.RatHurewicz.isEMSpaceUpTo_pi_fin
import Submission.Work.RatHurewicz.ConnectivityBridge
import Submission.Work.Pi6.EMODD.emSpaceTransport
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option linter.style.haveILetI false

open scoped Topology

namespace Work.Pi6.EMODD

namespace FibreAux

noncomputable section

/-- The section `mpathOf r : T → mpath r` of `mpathFst r` is a homotopy equivalence (with
`mpathFst r` as homotopy inverse).  This is the direction of `Work.FGThm.mpathHomotopyEquiv` in
which the base point is sent to the base point *on the nose*. -/
def mpathOfHomotopyEquiv {T X : Type} [TopologicalSpace T] [TopologicalSpace X] (r : C(T, X)) :
    ContinuousMap.HomotopyEquiv T (Work.Serre.mpath r) where
  toFun := Work.Serre.mpathOf r
  invFun := Work.Serre.mpathFst r
  left_inv := by
    rw [show (Work.Serre.mpathFst r).comp (Work.Serre.mpathOf r) = ContinuousMap.id T from rfl]
  right_inv := Work.FGThm.mpathOf_comp_mpathFst_homotopic r

/-- `Multiplicative.ofAdd 1` generates `Multiplicative R` for a ring `R`. -/
theorem ofAdd_one_zpow_ring {R : Type*} [Ring R] (n : ℤ) :
    (Multiplicative.ofAdd (1 : R) : Multiplicative R) ^ n = Multiplicative.ofAdd ((n : ℤ) : R) := by
  rw [← ofAdd_zsmul]
  congr 1
  rw [zsmul_eq_mul, mul_one]

/-- `Multiplicative.ofAdd 1` generates `Multiplicative ℤ`: its integral powers are the `ofAdd n`. -/
theorem ofAdd_one_zpow_int (n : ℤ) :
    (Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) ^ n = Multiplicative.ofAdd n := by
  rw [ofAdd_one_zpow_ring (R := ℤ) n, Int.cast_id]

/-- `Multiplicative.ofAdd 1` generates `Multiplicative (ZMod 2)`. -/
theorem ofAdd_one_zpow_zmodTwo (n : ℤ) :
    (Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) ^ n
      = Multiplicative.ofAdd ((n : ℤ) : ZMod 2) :=
  ofAdd_one_zpow_ring (R := ZMod 2) n

/-- Every element of `ZMod 2` is `0` or `1`. -/
theorem zmodTwo_cases_all : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

/-- Every element of `Multiplicative (ZMod 2)` is `1` or `ofAdd 1`. -/
theorem multZModTwo_cases (m : Multiplicative (ZMod 2)) :
    m = 1 ∨ m = Multiplicative.ofAdd (1 : ZMod 2) := by
  rcases zmodTwo_cases_all (Multiplicative.toAdd m) with h | h
  · left
    rw [← ofAdd_toAdd m, h]
    rfl
  · right
    rw [← ofAdd_toAdd m, h]

/-- **A non-trivial homomorphism into `Multiplicative (ZMod 2)` is surjective** (identified along
a group isomorphism `eB`): `Multiplicative (ZMod 2)` has exactly two elements. -/
theorem surjective_of_ne_one_of_mulEquiv_zmodTwo {G B : Type*} [Group G] [Group B]
    (f : G →* B) (eB : B ≃* Multiplicative (ZMod 2)) (hf : ∃ x : G, f x ≠ 1) :
    Function.Surjective f := by
  obtain ⟨x, hx⟩ := hf
  have hxne : eB (f x) ≠ 1 := fun h => hx (eB.injective (by rw [h, map_one]))
  have h1 : eB (f x) = Multiplicative.ofAdd (1 : ZMod 2) := by
    rcases multZModTwo_cases (eB (f x)) with h | h
    · exact absurd h hxne
    · exact h
  intro y
  rcases multZModTwo_cases (eB y) with h | h
  · exact ⟨1, eB.injective (by simp [h])⟩
  · exact ⟨x, eB.injective (by rw [h1, h])⟩

/-- **Triviality of `π_{k+1}` of the fibre of a Serre fibration, `k ≥ 1`**, from the long exact
homotopy sequence. -/
theorem subsingleton_pi_fibre_of_les {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (e₀ : E) {k : ℕ} (hk : 1 ≤ k)
    (hE : Subsingleton (HomotopyGroup (Fin (k + 1)) E e₀))
    (hB : Subsingleton (HomotopyGroup (Fin (k + 2)) B (p e₀))) :
    Subsingleton
      (HomotopyGroup (Fin (k + 1)) (Work.StemsB.fibre p (p e₀)) (Work.StemsB.fibrePoint p e₀)) := by
  have hLES : Work.StemsB.FibrationLES p e₀ :=
    Work.StemsB.fibrationLES_of_isSerreFibration p hp e₀
  obtain ⟨d, h1, h2, h3⟩ := hLES k
  haveI : Subsingleton (HomotopyGroup (Fin (k + 1)) E e₀) := hE
  haveI : Subsingleton (HomotopyGroup (Fin (k + 2)) B (p e₀)) := hB
  have key : ∀ a : HomotopyGroup (Fin (k + 1)) (Work.StemsB.fibre p (p e₀))
      (Work.StemsB.fibrePoint p e₀), a = 1 := by
    intro a
    haveI : Subsingleton (HomotopyGroup (Fin (k + 1)) E
        ((Work.StemsB.fibreIncl p (p e₀)) (Work.StemsB.fibrePoint p e₀))) := hE
    have ha : Work.StemsB.πmap (Work.StemsB.fibreIncl p (p e₀)) k (Work.StemsB.fibrePoint p e₀) a
        = 1 := Subsingleton.elim _ _
    obtain ⟨y, hy⟩ := (h3 a).mp ha
    have hy1 : y = 1 := Subsingleton.elim y 1
    rw [← hy, hy1, map_one]
  exact ⟨fun a b => by rw [key a, key b]⟩

/-- **Triviality of `π₁` of the fibre of a Serre fibration** when `π₁` of the total space is
trivial and `π₂(p)` is surjective. -/
theorem subsingleton_pi_one_fibre_of_les {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (e₀ : E)
    (hE1 : Subsingleton (HomotopyGroup (Fin 1) E e₀))
    (hb : Function.Surjective (Work.StemsB.πmap p 1 e₀)) :
    Subsingleton
      (HomotopyGroup (Fin 1) (Work.StemsB.fibre p (p e₀)) (Work.StemsB.fibrePoint p e₀)) := by
  have hLES : Work.StemsB.FibrationLES p e₀ :=
    Work.StemsB.fibrationLES_of_isSerreFibration p hp e₀
  obtain ⟨d0, h1, h2, h3⟩ := hLES 0
  haveI : Subsingleton (HomotopyGroup (Fin 1) E e₀) := hE1
  have key : ∀ a : HomotopyGroup (Fin 1) (Work.StemsB.fibre p (p e₀))
      (Work.StemsB.fibrePoint p e₀), a = 1 := by
    intro a
    haveI : Subsingleton (HomotopyGroup (Fin (0 + 1)) E
        ((Work.StemsB.fibreIncl p (p e₀)) (Work.StemsB.fibrePoint p e₀))) := hE1
    have ha : Work.StemsB.πmap (Work.StemsB.fibreIncl p (p e₀)) 0 (Work.StemsB.fibrePoint p e₀) a
        = 1 := Subsingleton.elim _ _
    obtain ⟨y, hy⟩ := (h3 a).mp ha
    obtain ⟨y', hy'⟩ := hb y
    have hdy : d0 y = 1 := (h2 y).mpr ⟨y', hy'⟩
    rw [← hy, hdy]
  exact ⟨fun a b => by rw [key a, key b]⟩

/-- **The kernel of a surjection `ℤ ↠ ℤ/2` is infinite cyclic.** -/
theorem int_of_exact_zmodTwo {F E B : Type*} [Group F] [Group E] [Group B]
    (a : F →* E) (ha : Function.Injective a) (b : E →* B) (hex : Function.MulExact a b)
    (hb : Function.Surjective b) (eE : E ≃* Multiplicative ℤ)
    (eB : B ≃* Multiplicative (ZMod 2)) :
    Nonempty (F ≃* Multiplicative ℤ) := by
  classical
  set g : E := eE.symm (Multiplicative.ofAdd (1 : ℤ)) with hg
  have hsymm_zpow : ∀ n : ℤ, eE.symm (Multiplicative.ofAdd n) = g ^ n := by
    intro n
    rw [← ofAdd_one_zpow_int n, map_zpow]
  have hE_zpow : ∀ n : ℤ, eE (g ^ n) = Multiplicative.ofAdd n := by
    intro n
    rw [← hsymm_zpow n, MulEquiv.apply_symm_apply]
  have hgen : ∀ y : E, ∃ n : ℤ, y = g ^ n := by
    intro y
    refine ⟨(eE y).toAdd, ?_⟩
    rw [← hsymm_zpow, ofAdd_toAdd, MulEquiv.symm_apply_apply]
  set F2 : Multiplicative ℤ →* Multiplicative (ZMod 2) :=
    (eB.toMonoidHom.comp b).comp eE.symm.toMonoidHom with hF2def
  have hF2_apply : ∀ x : Multiplicative ℤ, F2 x = eB (b (eE.symm x)) := fun x => rfl
  have hF2_surj : Function.Surjective F2 := by
    intro y
    obtain ⟨a1, ha1⟩ : ∃ a1 : B, eB a1 = y := ⟨eB.symm y, eB.apply_symm_apply y⟩
    obtain ⟨a2, ha2⟩ : ∃ a2 : E, b a2 = a1 := hb a1
    refine ⟨eE a2, ?_⟩
    rw [hF2_apply, MulEquiv.symm_apply_apply, ha2, ha1]
  have hbg_ne : b g ≠ 1 := by
    intro hc
    have htriv : ∀ y : E, b y = 1 := by
      intro y
      obtain ⟨n, rfl⟩ := hgen y
      rw [map_zpow, hc, one_zpow]
    have hnt : (Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) ≠ 1 := by
      rw [Ne, ofAdd_eq_one]
      decide
    obtain ⟨y₀, hy₀⟩ : ∃ y₀ : E, b y₀ = eB.symm (Multiplicative.ofAdd (1 : ZMod 2)) :=
      hb (eB.symm (Multiplicative.ofAdd (1 : ZMod 2)))
    rw [htriv y₀] at hy₀
    refine hnt ?_
    rw [← eB.apply_symm_apply (Multiplicative.ofAdd (1 : ZMod 2)), ← hy₀, map_one]
  have hF2_one : F2 (Multiplicative.ofAdd (1 : ℤ)) = Multiplicative.ofAdd (1 : ZMod 2) := by
    rcases multZModTwo_cases (F2 (Multiplicative.ofAdd (1 : ℤ))) with h | h
    · exfalso
      have hbg1 : b g = 1 := by
        have h5 : eB (b g) = 1 := by
          rw [hg, ← hF2_apply (Multiplicative.ofAdd (1 : ℤ)), h]
        exact eB.injective (by rw [h5, map_one])
      exact hbg_ne hbg1
    · exact h
  have hF2_val : ∀ n : ℤ, F2 (Multiplicative.ofAdd n) = Multiplicative.ofAdd ((n : ℤ) : ZMod 2) := by
    intro n
    rw [← ofAdd_one_zpow_int n, map_zpow, hF2_one, ofAdd_one_zpow_zmodTwo n]
  have hpar : ∀ n : ℤ, b (g ^ n) = 1 ↔ (2 : ℤ) ∣ n := by
    intro n
    have h1 : eB (b (g ^ n)) = F2 (Multiplicative.ofAdd n) := by
      simp only [hF2_apply, hsymm_zpow]
    have h2 : eB (b (g ^ n)) = 1 ↔ b (g ^ n) = 1 := by
      constructor
      · intro hh; exact eB.injective (by rw [hh, map_one])
      · intro hh; rw [hh, map_one]
    have h2Z : ((2 : ℕ) : ℤ) = (2 : ℤ) := by norm_num
    rw [← h2, h1, hF2_val n, ofAdd_eq_one, ZMod.intCast_zmod_eq_zero_iff_dvd n 2, h2Z]
  have hbg2 : b (g ^ (2 : ℤ)) = 1 := (hpar 2).mpr ⟨1, by norm_num⟩
  obtain ⟨z, hz⟩ := (hex (g ^ (2 : ℤ))).mp hbg2
  have ha_zpow : ∀ m : ℤ, a (z ^ m) = g ^ (2 * m) := by
    intro m
    rw [map_zpow, hz, ← zpow_mul]
  let phi : Multiplicative ℤ →* F :=
    { toFun := fun m => z ^ (Multiplicative.toAdd m)
      map_one' := by simp
      map_mul' := fun m m' => by
        show z ^ (Multiplicative.toAdd (m * m')) = z ^ (Multiplicative.toAdd m)
          * z ^ (Multiplicative.toAdd m')
        rw [toAdd_mul, zpow_add] }
  have hphi_apply : ∀ m : ℤ, phi (Multiplicative.ofAdd m) = z ^ m := fun m => rfl
  have hphi_inj : Function.Injective phi := by
    intro m m' hmm
    have hmm' : z ^ (Multiplicative.toAdd m) = z ^ (Multiplicative.toAdd m') := hmm
    have h7 : z ^ (Multiplicative.toAdd m - Multiplicative.toAdd m') = 1 := by
      rw [sub_eq_add_neg, zpow_add, zpow_neg, hmm', mul_inv_cancel]
    have h6 : Multiplicative.ofAdd
        (2 * (Multiplicative.toAdd m - Multiplicative.toAdd m')) = 1 := by
      rw [← hE_zpow (2 * (Multiplicative.toAdd m - Multiplicative.toAdd m')),
        ← ha_zpow (Multiplicative.toAdd m - Multiplicative.toAdd m'), h7, map_one, map_one]
    have h8 : 2 * (Multiplicative.toAdd m - Multiplicative.toAdd m') = 0 := by
      have h9 := congrArg Multiplicative.toAdd h6
      simpa using h9
    have h10 : Multiplicative.toAdd m = Multiplicative.toAdd m' := by omega
    exact Multiplicative.toAdd.injective h10
  have hphi_surj : Function.Surjective phi := by
    intro x
    obtain ⟨n, hn⟩ := hgen (a x)
    have hbn : (2 : ℤ) ∣ n := by
      have hmem : g ^ n ∈ Set.range a := ⟨x, hn⟩
      exact (hpar n).mp ((hex (g ^ n)).mpr hmem)
    obtain ⟨m, hm⟩ := hbn
    refine ⟨Multiplicative.ofAdd m, ?_⟩
    rw [hphi_apply m]
    exact ha (by rw [ha_zpow m, ← hm, hn])
  exact ⟨(MulEquiv.ofBijective phi ⟨hphi_inj, hphi_surj⟩).symm⟩

/-- `π_j` of the mapping path space `mpath r` is trivial when `π_j T` is (`j ≥ 1`). -/
theorem subsingleton_pi_mpath {T X : Type} [TopologicalSpace T] [TopologicalSpace X]
    (r : C(T, X)) (k₀ : T) {j : ℕ} (hj : 1 ≤ j)
    (h : Subsingleton (HomotopyGroup (Fin j) T k₀)) :
    Subsingleton (HomotopyGroup (Fin j) (Work.Serre.mpath r) (mpathPt r k₀)) := by
  haveI : Nonempty (Fin j) := ⟨⟨0, hj⟩⟩
  obtain ⟨e⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin j) (mpathOfHomotopyEquiv r) k₀
  haveI := h
  exact ⟨fun a b => e.symm.injective (Subsingleton.elim _ _)⟩

/-- `π_2` of the mapping path space `mpath r` is `Multiplicative ℤ` when `π_2 T` is. -/
theorem piTwo_mpath {T X : Type} [TopologicalSpace T] [TopologicalSpace X]
    (r : C(T, X)) (k₀ : T)
    (h : Nonempty (HomotopyGroup (Fin 2) T k₀ ≃* Multiplicative ℤ)) :
    Nonempty (HomotopyGroup (Fin 2) (Work.Serre.mpath r) (mpathPt r k₀) ≃* Multiplicative ℤ) := by
  obtain ⟨e⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin 2) (mpathOfHomotopyEquiv r) k₀
  exact ⟨e.symm.trans h.some⟩

/-- **`π₂(r)` is surjective** whenever it is non-trivial: `π₂(T)` is infinite cyclic, `π₂(X)` has
two elements, so a non-zero homomorphism between them is surjective. -/
theorem surjective_piTwo_of_ne_one {T X : Type} [TopologicalSpace T] [TopologicalSpace X]
    (r : C(T, X)) (k₀ : T) (eX : HomotopyGroup (Fin 2) X (r k₀) ≃* Multiplicative (ZMod 2))
    (hπ : ∃ a : HomotopyGroup (Fin 2) T k₀, Work.StemsB.πmap r 1 k₀ a ≠ 1) :
    Function.Surjective (Work.StemsB.πmap r 1 k₀) :=
  surjective_of_ne_one_of_mulEquiv_zmodTwo _ eX
    (by obtain ⟨a, ha⟩ := hπ
        exact ⟨a, fun h => ha (eX.injective (by rw [h, map_one]))⟩)

/-- **The map `π₂(mpath r) → π₂(X)` induced by the mapping-path projection is surjective**, because
it agrees (along the section `mpathOf r`) with the non-trivial map `π₂(r)`. -/
theorem surjective_piTwo_mpathQ {T X : Type} [TopologicalSpace T] [TopologicalSpace X]
    (r : C(T, X)) (k₀ : T) (eX : HomotopyGroup (Fin 2) X (r k₀) ≃* Multiplicative (ZMod 2))
    (hπ : ∃ a : HomotopyGroup (Fin 2) T k₀, Work.StemsB.πmap r 1 k₀ a ≠ 1) :
    Function.Surjective (Work.StemsB.πmap (Work.Serre.mpathQ r) 1 (mpathPt r k₀)) := by
  have hsurj := surjective_piTwo_of_ne_one r k₀ eX hπ
  have heq_of_comp : ∀ b : HomotopyGroup (Fin 2) T k₀,
      Work.StemsB.πmap (Work.Serre.mpathQ r) 1 (mpathPt r k₀)
        (Work.StemsB.πmap (Work.Serre.mpathOf r) 1 k₀ b) = Work.StemsB.πmap r 1 k₀ b := by
    intro b
    induction b using Quotient.inductionOn with
    | h γ =>
      rw [Work.StemsB.πmap_apply_mk, Work.StemsB.πmap_apply_mk, Work.StemsB.πmap_apply_mk]
      rfl
  intro y
  obtain ⟨b, hb⟩ := hsurj y
  refine ⟨Work.StemsB.πmap (Work.Serre.mpathOf r) 1 k₀ b, ?_⟩
  rw [heq_of_comp b]
  exact hb

end

end FibreAux

/-- **The fibre of the mapping-path fibration of a map between a `K(ℤ,2)`- and a `K(ℤ/2,2)`-model.** Let `r : T → X` have `T` a range model of `K(ℤ,2)` through `N ≥ 10` and `X` a range model of `K(ℤ/2,2)` through `N`, both at the base point, and suppose `π₂(r) ≠ 0`. For the Serre fibration `Work.Serre.mpathQ r : Work.Serre.mpath r → X` (whose total is homotopy equivalent to `T` by `Work.FGThm.mpathHomotopyEquiv`): the strict fibre `mpathFibre r k₀` (defined in `Submission/Work/Pi6/EMODD/Defs.lean`) is a range model of `K(ℤ,2)` through `N - 1` at `mpathFibrePt r k₀` (the LES `Work.StemsB.FibrationLES` gives `π₂ ≅ ker (π₂ r) ≅ ℤ` and `π_i = 0` for `1 ≤ i ≤ N-1`, `i ≠ 2`; the `π₀` clause of `IsEMSpaceUpTo` needs the path connectedness of the fibre, e.g. `Work.Serre.subsingleton_pi0_homotopyFibre` / `Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration`), the fibre inclusion is non-trivial on `π₂`, and the total space `mpath r` is a range model of `K(ℤ,2)` through `N` (`Work.FGThm.mpathHomotopyEquiv` together with a range transport of `IsEMSpaceUpTo` along a homotopy equivalence, cf. `Submission/Work/Pi6/EMODD/emSpaceTransport.lean`). The strict fibre is homeomorphic to `Work.RatHurewicz.homotopyFibre r k₀` by `Work.Serre.mpathQ_fibreHomeo`, which is the route to the `π`-computation. -/
theorem fibreOfMpathQ (N : ℕ) (hN : 10 ≤ N) {T X : Type} [TopologicalSpace T]
    [TopologicalSpace X] (r : C(T, X)) (k₀ : T)
    (hT : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) N T k₀)
    (hX : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) N X (r k₀))
    (hπ : ∃ a : HomotopyGroup (Fin 2) T k₀, Work.StemsB.πmap r 1 k₀ a ≠ 1) :
    Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) (N - 1)
        (Work.Pi6.EMODD.mpathFibre r k₀) (Work.Pi6.EMODD.mpathFibrePt r k₀) ∧
      (∃ b : HomotopyGroup (Fin 2) (Work.Pi6.EMODD.mpathFibre r k₀)
          (Work.Pi6.EMODD.mpathFibrePt r k₀),
        Work.StemsB.πmap (Work.StemsB.fibreIncl (Work.Serre.mpathQ r)
          (Work.Serre.mpathQ r (Work.Pi6.EMODD.mpathPt r k₀))) 1
          (Work.Pi6.EMODD.mpathFibrePt r k₀) b ≠ 1) ∧
      Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) N (Work.Serre.mpath r)
        (Work.Pi6.EMODD.mpathPt r k₀) := by
  classical
  -- ## The total space `mpath r` is a range model of `K(ℤ,2)` through `N`
  have hmpath : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) N (Work.Serre.mpath r)
      (mpathPt r k₀) :=
    emSpaceTransport ℤ 2 (by norm_num) N (FibreAux.mpathOfHomotopyEquiv r) rfl hT
  -- ## Path connectedness of the total space, the base and the fibre
  haveI hpcE : PathConnectedSpace (Work.Serre.mpath r) :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero (mpathPt r k₀)
      (hmpath.2 0 (by norm_num) (Or.inl (by norm_num)))
  haveI hpcB : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero (r k₀)
      (hX.2 0 (by norm_num) (Or.inl (by norm_num)))
  have hserre : Work.StemsB.IsSerreFibration (Work.Serre.mpathQ r) :=
    Work.Serre.mpathQ_isSerreFibration r
  haveI hpcF : PathConnectedSpace (mpathFibre r k₀) :=
    Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration (Work.Serre.mpathQ r) hserre
      ((Work.Serre.mpathQ r) (mpathPt r k₀)) hpcE hpcB
      (hX.2 1 (by norm_num) (Or.inl (by norm_num)))
  -- ## The long exact homotopy sequence of `mpathQ r`
  have hLES : Work.StemsB.FibrationLES (Work.Serre.mpathQ r) (mpathPt r k₀) :=
    Work.StemsB.fibrationLES_of_isSerreFibration (Work.Serre.mpathQ r) hserre (mpathPt r k₀)
  obtain ⟨d0, hex1_0, hex2_0, hex3_0⟩ := hLES 0
  obtain ⟨d1, hex1_1, hex2_1, hex3_1⟩ := hLES 1
  -- ## `π₂(mpathQ r)` is onto
  have hsurj : Function.Surjective (Work.StemsB.πmap (Work.Serre.mpathQ r) 1 (mpathPt r k₀)) :=
    FibreAux.surjective_piTwo_mpathQ r k₀ hX.1.some hπ
  -- ## the fibre inclusion is injective on `π₂`
  have hinjπ2 : Function.Injective (Work.StemsB.πmap (Work.StemsB.fibreIncl (Work.Serre.mpathQ r)
      ((Work.Serre.mpathQ r) (mpathPt r k₀))) 1 (mpathFibrePt r k₀)) := by
    intro x y hxy
    haveI : Subsingleton (HomotopyGroup (Fin 3) X ((Work.Serre.mpathQ r) (mpathPt r k₀))) :=
      hX.2 3 (by norm_num) (Or.inr (by omega))
    have h1 : (Work.StemsB.πmap (Work.StemsB.fibreIncl (Work.Serre.mpathQ r)
        ((Work.Serre.mpathQ r) (mpathPt r k₀))) 1 (mpathFibrePt r k₀)) (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hmem : x * y⁻¹ ∈ Set.range d1 := (hex3_1 (x * y⁻¹)).mp h1
    obtain ⟨w, hw⟩ := hmem
    have hw1 : x * y⁻¹ = 1 := by rw [← hw, Subsingleton.elim w 1, map_one]
    exact mul_inv_eq_one.mp hw1
  -- ## `π₂` of the fibre is infinite cyclic
  have hpi2 : Nonempty (HomotopyGroup (Fin 2) (mpathFibre r k₀) (mpathFibrePt r k₀)
      ≃* Multiplicative ℤ) :=
    FibreAux.int_of_exact_zmodTwo
      (Work.StemsB.πmap (Work.StemsB.fibreIncl (Work.Serre.mpathQ r)
        ((Work.Serre.mpathQ r) (mpathPt r k₀))) 1 (mpathFibrePt r k₀))
      hinjπ2 (Work.StemsB.πmap (Work.Serre.mpathQ r) 1 (mpathPt r k₀)) hex1_0 hsurj
      (FibreAux.piTwo_mpath r k₀ hT.1).some hX.1.some
  -- ## `π₁` of the fibre is trivial
  have hpi1 : Subsingleton (HomotopyGroup (Fin 1) (mpathFibre r k₀) (mpathFibrePt r k₀)) :=
    FibreAux.subsingleton_pi_one_fibre_of_les (Work.Serre.mpathQ r) hserre (mpathPt r k₀)
      (hmpath.2 1 (by norm_num) (Or.inl (by norm_num))) hsurj
  -- ## `π₀` of the fibre is trivial
  have hpi0 : Subsingleton (HomotopyGroup (Fin 0) (mpathFibre r k₀) (mpathFibrePt r k₀)) := by
    have hZ : Subsingleton (ZerothHomotopy (mpathFibre r k₀)) :=
      (pathConnectedSpace_iff_zerothHomotopy (X := mpathFibre r k₀)).mp hpcF |>.2
    exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (X := mpathFibre r k₀)
      (x := mpathFibrePt r k₀)).injective (hZ.elim _ _)⟩
  -- ## `π_i` of the fibre for `3 ≤ i ≤ N - 1`
  have hvan : ∀ i : ℕ, 3 ≤ i → i ≤ N - 1 →
      Subsingleton (HomotopyGroup (Fin i) (mpathFibre r k₀) (mpathFibrePt r k₀)) := by
    intro i hi3 hiN
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 :=
      ⟨i - 1, (Nat.sub_add_cancel (by omega : 1 ≤ i)).symm⟩
    refine FibreAux.subsingleton_pi_fibre_of_les (Work.Serre.mpathQ r) hserre (mpathPt r k₀)
      (k := k) (by omega) ?_ ?_
    · exact FibreAux.subsingleton_pi_mpath r k₀ (j := k + 1) (by omega)
        (hT.2 (k + 1) (by omega) (Or.inr (by omega)))
    · exact hX.2 (k + 2) (by omega) (Or.inr (by omega))
  refine ⟨⟨hpi2, ?_⟩, ?_, hmpath⟩
  · intro i hi2 hc
    by_cases hi0 : i = 0
    · subst hi0; exact hpi0
    by_cases hi1 : i = 1
    · subst hi1; exact hpi1
    exact hvan i (by omega) (hc.resolve_left (by omega))
  · obtain ⟨eF⟩ := hpi2
    have hne1 : (Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) ≠ 1 := by
      rw [Ne, ofAdd_eq_one]
      decide
    refine ⟨eF.symm (Multiplicative.ofAdd 1), fun hh => ?_⟩
    have h3 : eF.symm (Multiplicative.ofAdd (1 : ℤ)) = 1 := hinjπ2 (by rw [hh, map_one])
    have h4 : (Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) = 1 := by
      calc (Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ)
          = eF (eF.symm (Multiplicative.ofAdd (1 : ℤ))) :=
            (MulEquiv.apply_symm_apply eF _).symm
        _ = eF 1 := by rw [h3]
        _ = 1 := map_one eF
    exact hne1 h4

end Work.Pi6.EMODD
