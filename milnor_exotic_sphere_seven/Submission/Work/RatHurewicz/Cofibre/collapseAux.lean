import Mathlib
import Submission.Work.StemsB.PiMap

import Submission.Work.Stems.HomotopyGroupMap
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv
import Submission.Work.Serre.rwPiMapN_bijective_of_homotopyEquiv
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.StemsB.fibration_les
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.RatHurewicz.Cofibre.ConeContract
import Submission.Work.Stems.subsingleton_homotopyGroup_change_basepoint

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false

/-!
# Toolbox for the cofibre collapse: `π`-transport along commuting squares

* `Work.RatHurewicz.Cofibre.πmap_eq_map`: the workspace's `Work.StemsB.πmap` is (the workspace's)
  `HomotopyGroup.map`;
* `πmap_square_apply`: the compatibility of a commuting square `x ∘ g₁ = g₂ ∘ a` with the induced
  maps on homotopy groups;
* `injective_πmap_of_square` / `surjective_πmap_of_square`: injectivity (resp. surjectivity) of the
  map induced by the bottom arrow of a commuting square transfers to the top arrow, provided the
  two vertical arrows induce bijections on homotopy groups.
-/

open scoped Topology

namespace Work.RatHurewicz.Cofibre

/-- **`Work.StemsB.πmap` is `HomotopyGroup.map`**: the workspace's named induced map agrees with the
one used by `Work.Stems.mulEquiv_of_homotopyEquiv`. -/
theorem πmap_eq_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) (x : X) :
    Work.StemsB.πmap f n x = HomotopyGroup.map (N := Fin (n + 1)) (x := x) f := by
  funext a
  induction a using Quotient.inductionOn with
  | h γ => rfl

/-- **A homotopy equivalence induces a bijection on homotopy groups** (for the workspace's
`Work.StemsB.πmap`), obtained from `Work.Serre.rwPiMapN_bijective_of_homotopyEquiv` (which is about
`Work.Serre.piMapN`) and the identification `Work.Serre.piMapN_eq_homotopyGroupMap`. -/
theorem bijective_pimap_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (m : ℕ) (x : X) :
    Function.Bijective (Work.StemsB.πmap e.toFun m x) := by
  have h := Work.Serre.rwPiMapN_bijective_of_homotopyEquiv (X := X) (Y := Y) e (m + 1) x
  have h1 : Work.Serre.piMapN e.toFun (m + 1) x
      = HomotopyGroup.map (N := Fin (m + 1)) (x := x) e.toFun :=
    Work.Serre.piMapN_eq_homotopyGroupMap e.toFun (m + 1) x
  rw [πmap_eq_map]
  rw [← h1]
  exact h

section square

variable {A₁ X₁ A₂ X₂ : Type*} [TopologicalSpace A₁] [TopologicalSpace X₁]
  [TopologicalSpace A₂] [TopologicalSpace X₂]

/-- The key compatibility of a commuting square `x ∘ g₁ = g₂ ∘ a` with the induced maps on
homotopy groups: the two composites agree up to the base-point transport along the square. -/
theorem πmap_square_apply (g₁ : C(A₁, X₁)) (g₂ : C(A₂, X₂)) (a : C(A₁, A₂)) (x : C(X₁, X₂))
    (hsq : x.comp g₁ = g₂.comp a) (n : ℕ) (α : A₁)
    (w : HomotopyGroup (Fin (n + 1)) A₁ α) :
    Work.StemsB.homotopyGroupCast (congrArg (fun k : C(A₁, X₂) => k α) hsq) n
        (Work.StemsB.πmap x n (g₁ α) (Work.StemsB.πmap g₁ n α w))
      = Work.StemsB.πmap g₂ n (a α) (Work.StemsB.πmap a n α w) := by
  rw [← Work.StemsB.πmap_comp_apply g₁ x n α w,
    ← Work.StemsB.πmap_comp_apply a g₂ n α w]
  exact Work.StemsB.πmap_congr hsq n α w

/-- **Injectivity transfers along a commuting square.**  If the map induced by `g₂` at the base
point `a α` is injective and the vertical map `a` induces an injection on homotopy groups, then the
map induced by `g₁` at `α` is injective as well. -/
theorem injective_πmap_of_square (g₁ : C(A₁, X₁)) (g₂ : C(A₂, X₂)) (a : C(A₁, A₂))
    (x : C(X₁, X₂)) (hsq : x.comp g₁ = g₂.comp a) (n : ℕ) (α : A₁)
    (ha : Function.Injective (Work.StemsB.πmap a n α))
    (h : Function.Injective (Work.StemsB.πmap g₂ n (a α))) :
    Function.Injective (Work.StemsB.πmap g₁ n α) := by
  intro u v huv
  have hx : Work.StemsB.homotopyGroupCast (congrArg (fun k : C(A₁, X₂) => k α) hsq) n
        (Work.StemsB.πmap x n (g₁ α) (Work.StemsB.πmap g₁ n α u))
      = Work.StemsB.homotopyGroupCast (congrArg (fun k : C(A₁, X₂) => k α) hsq) n
        (Work.StemsB.πmap x n (g₁ α) (Work.StemsB.πmap g₁ n α v)) := by rw [huv]
  rw [πmap_square_apply g₁ g₂ a x hsq n α u,
    πmap_square_apply g₁ g₂ a x hsq n α v] at hx
  exact ha (h hx)

/-- **Surjectivity transfers along a commuting square.**  If the map induced by `g₂` at `a α` is
surjective, the vertical maps induce on homotopy groups a surjection (`a`) and an injection (`x`),
then the map induced by `g₁` at `α` is surjective as well. -/
theorem surjective_πmap_of_square (g₁ : C(A₁, X₁)) (g₂ : C(A₂, X₂)) (a : C(A₁, A₂))
    (x : C(X₁, X₂)) (hsq : x.comp g₁ = g₂.comp a) (n : ℕ) (α : A₁)
    (ha : Function.Surjective (Work.StemsB.πmap a n α))
    (hx : Function.Injective (Work.StemsB.πmap x n (g₁ α)))
    (h : Function.Surjective (Work.StemsB.πmap g₂ n (a α))) :
    Function.Surjective (Work.StemsB.πmap g₁ n α) := by
  intro y
  set e := congrArg (fun k : C(A₁, X₂) => k α) hsq with he
  obtain ⟨w, hw⟩ := h (Work.StemsB.homotopyGroupCast e n (Work.StemsB.πmap x n (g₁ α) y))
  obtain ⟨u, hu⟩ := ha w
  refine ⟨u, ?_⟩
  have key := πmap_square_apply g₁ g₂ a x hsq n α u
  rw [← hu] at hw
  rw [hw] at key
  exact hx ((Work.StemsB.homotopyGroupCast e n).injective key)

end square

end Work.RatHurewicz.Cofibre

/-! ## The low-degree consequences of the long exact sequence of a pair

The workspace's `Work.RatHurewicz.pair_les` states the long exact sequence of a pair only from
degree `3` on (its index `k` satisfies `1 ≤ k`).  The two lemmas below supply what is missing in
degrees `1` and `2`, in the form in which the collapse computation needs it: the vanishing of the
relative groups of `i : C(A,X)` in degrees `n` and `n+1` makes `π_{n+1}(i)` bijective.  They are
read off the long exact sequence of the *fibration* `homotopyFibreFst i a₀`
(`Work.StemsB.les_exact_B` and `Work.StemsB.les_exact_F`), together with
`Work.RatHurewicz.fibreDMap_eq_pairShiftHom` (the connecting map of that fibration is `i_*` after
the loop-space shift) and the bijectivity of the loop-space shift
`Work.RatHurewicz.pairShiftHom_bijective`. -/

namespace Work.RatHurewicz.Cofibre

open Work.StemsB

/-- **Injectivity from the vanishing of the relative group one degree up**: if
`RelHomotopyGroup i a₀ (n+1)` is trivial (`n ≥ 1`) then `π_{n+1}(i)` is injective. -/
theorem injective_πmap_of_relPi_subsingleton {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (i : C(A, X)) (a₀ : A) (n : ℕ) (hn : 1 ≤ n)
    (hrel' : Subsingleton (RelHomotopyGroup i a₀ (n + 1))) :
    Function.Injective (πmap i n a₀) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hd : dMap (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀) (fibreHrel i a₀) m
      = (pairShiftHom i a₀ m).comp (πmap i (m + 1) a₀) :=
    fibreDMap_eq_pairShiftHom i a₀ m
  intro u v huv
  have hw : πmap i (m + 1) a₀ (u * v⁻¹) = 1 := by
    rw [map_mul, map_inv, huv, mul_inv_cancel]
  have hker : dMap (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀) (fibreHrel i a₀) m
      (u * v⁻¹) = 1 := by
    rw [hd]
    exact (congrArg (fun t => pairShiftHom i a₀ m t) hw).trans (map_one _)
  have hE := les_exact_B (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀)
    (fibreHrel i a₀) m
  obtain ⟨z, hz⟩ := (hE (u * v⁻¹)).mp hker
  have hz1 : z = 1 := hrel'.elim z 1
  have huv1 : u * v⁻¹ = 1 := by rw [← hz, hz1, map_one]
  exact mul_inv_eq_one.mp huv1

/-- **Surjectivity from the vanishing of the relative group in the same degree**: if
`RelHomotopyGroup i a₀ n` is trivial (`n ≥ 1`) then `π_{n+1}(i)` is surjective. -/
theorem surjective_πmap_of_relPi_subsingleton {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (i : C(A, X)) (a₀ : A) (n : ℕ) (hn : 1 ≤ n)
    (hrel : Subsingleton (RelHomotopyGroup i a₀ n)) :
    Function.Surjective (πmap i n a₀) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hd : dMap (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀) (fibreHrel i a₀) m
      = (pairShiftHom i a₀ m).comp (πmap i (m + 1) a₀) :=
    fibreDMap_eq_pairShiftHom i a₀ m
  have hP : Function.Injective (pairShiftHom i a₀ m) :=
    (pairShiftHom_bijective i a₀ m).1
  intro y
  have hF := les_exact_F (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀)
    (fibreHrel i a₀) m
  have hker : πmap (Work.StemsB.fibreIncl (homotopyFibreFst i a₀)
        ((homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀))) m
        (Work.StemsB.fibrePoint (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀))
        (pairShiftHom i a₀ m y) = 1 := hrel.elim _ 1
  obtain ⟨u, hu⟩ := (hF (pairShiftHom i a₀ m y)).mp hker
  refine ⟨u, ?_⟩
  apply hP
  rw [← hu, hd]
  rfl

/-- **The low-degree pair sequence**: if the relative groups of the pair `i : C(A,X)` vanish in
degrees `n` and `n+1` (`n ≥ 1`), then `π_{n+1}(i)` is bijective. -/
theorem bijective_πmap_of_relPi_subsingleton {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (i : C(A, X)) (a₀ : A) (n : ℕ) (hn : 1 ≤ n)
    (hrel : Subsingleton (RelHomotopyGroup i a₀ n))
    (hrel' : Subsingleton (RelHomotopyGroup i a₀ (n + 1))) :
    Function.Bijective (πmap i n a₀) :=
  ⟨injective_πmap_of_relPi_subsingleton i a₀ n hn hrel',
    surjective_πmap_of_relPi_subsingleton i a₀ n hn hrel⟩

end Work.RatHurewicz.Cofibre

namespace Work.RatHurewicz.Cofibre

open scoped Topology Topology.Homotopy unitInterval

/-- **Compression in dimension `j+1` makes `π_{j+1}(f)` surjective**, for a map `f : C(A,X)` with a
continuous *section* `S` of the range parametrisation.

This is the proof of `Work.RatHurewicz.Cofibre.surjective_pimap_of_compressRel_range`
(`Submission/Work/RatHurewicz/Cofibre/piMap_cofibreCollapse_bijective.lean`), reproduced here
because that module (transitively) imports `Submission.Work.ThomBordism.TwoSet.Setup`, which cannot
be imported together with the `Triad.SpreadDefs` closure of `RatHurewicz.Cofibre.StableRangeDefs`. -/
theorem surjective_pimap_of_compressRel_range' {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (f : C(A, X)) (a₀ : A) (n : ℕ)
    (h : ∀ d, d ≤ n → Work.RatHurewicz.CompressRel X (Set.range ⇑f) d)
    (S : C(↥(Set.range ⇑f), A)) (hS : ∀ b, f (S b) = b.1)
    (hS₀ : S ⟨f a₀, ⟨a₀, rfl⟩⟩ = a₀) (j : ℕ) (hj : j + 1 ≤ n) :
    Function.Surjective (Work.StemsB.πmap f j a₀) := by
  intro y
  induction y using Quotient.inductionOn with
  | h g =>
    have hbdf : ∀ x, x ∈ Cube.boundary (Fin (j + 1)) → g.1 x ∈ Set.range ⇑f := by
      intro x hx
      rw [g.2 x hx]
      exact ⟨a₀, rfl⟩
    obtain ⟨G, hG0, hGb, hG1⟩ := h (j + 1) hj g.1 hbdf
    let g' : Ω^ (Fin (j + 1)) A a₀ :=
      ⟨⟨fun x => S ⟨G (x, 1), hG1 x⟩, by fun_prop⟩, by
        intro x hx
        show S ⟨G (x, 1), hG1 x⟩ = a₀
        have hx1 : G (x, 1) = f a₀ := by rw [hGb x hx 1]; exact g.2 x hx
        have hxe : (⟨G (x, 1), hG1 x⟩ : ↥(Set.range ⇑f)) = ⟨f a₀, ⟨a₀, rfl⟩⟩ := Subtype.ext hx1
        rw [hxe, hS₀]⟩
    refine ⟨⟦g'⟧, ?_⟩
    rw [Work.StemsB.πmap_apply_mk]
    apply Quotient.sound
    have hhom : (g.1).HomotopicRel ((Work.StemsB.genLoopMap f (j + 1) g').1)
        (Cube.boundary (Fin (j + 1))) := by
      refine ⟨{ toHomotopy := { toFun := fun p => G (p.2, p.1), continuous_toFun := ?_, map_zero_left := ?_, map_one_left := ?_ }, prop' := ?_ }⟩
      · fun_prop
      · intro x
        show G (x, 0) = g.1 x
        exact hG0 x
      · intro x
        show G (x, 1) = f (g' x)
        exact (hS ⟨G (x, 1), hG1 x⟩).symm
      · intro t x hx
        show G (x, t) = g.1 x
        exact hGb x hx t
    exact hhom.symm

end Work.RatHurewicz.Cofibre

namespace Work.RatHurewicz.Cofibre

/-- **A contraction to a point makes the homotopy groups trivial at every point**: the path traced
by a point under the contraction joins it to the contraction point. -/
theorem subsingleton_homotopyGroup_of_contraction' {N X : Type} [TopologicalSpace X]
    {X' : Type} [TopologicalSpace X'] (H : C(X × unitInterval, X)) (b : X)
    (h0 : ∀ x, H (x, 0) = x) (h1 : ∀ x, H (x, 1) = b) (hb : ∀ t, H (b, t) = b) (v : X) :
    Subsingleton (HomotopyGroup N X v) := by
  have γ : Path v b :=
    ⟨⟨fun t => H (v, t), H.continuous.comp (continuous_const.prodMk continuous_id)⟩,
      h0 v, h1 v⟩
  exact Work.Stems.subsingleton_homotopyGroup_change_basepoint γ.symm
    (subsingleton_homotopyGroup_of_contraction H b h0 h1 hb)

end Work.RatHurewicz.Cofibre

namespace Work.RatHurewicz.Cofibre

/-- **A contraction to a point makes the homotopy groups trivial at every point** (no hypothesis
that the contraction fixes the base point).  The homotopy `H` witnesses that the identity of `X` is
homotopic to the constant map at `b`, so by
`Work.Stems.Pinch.transport_map` the base-point transport along the path traced by `v` kills every
element of `π_N(X,v)`. -/
theorem subsingleton_homotopyGroup_of_contraction'' {N : Type} [DecidableEq N] [Nonempty N]
    [Fintype N] {X : Type} [TopologicalSpace X]
    (H : C(X × unitInterval, X)) (b : X) (h0 : ∀ x, H (x, 0) = x) (h1 : ∀ x, H (x, 1) = b)
    (v : X) : Subsingleton (HomotopyGroup N X v) := by
  have hH : (ContinuousMap.id X).Homotopy (ContinuousMap.const X b) :=
    { toContinuousMap := ⟨fun p : unitInterval × X => H (p.2, p.1),
        H.continuous.comp (continuous_snd.prodMk continuous_fst)⟩,
      map_zero_left := fun x => h0 x,
      map_one_left := fun x => h1 x }
  have hconst : ∀ a : HomotopyGroup N X v,
      HomotopyGroup.map (ContinuousMap.const X b) a = 1 := by
    intro a
    induction a using Quotient.inductionOn with
    | h γ =>
      rw [HomotopyGroup.map_mk_mapLoop, HomotopyGroup.one_def]
      congr 1
  have key : ∀ a : HomotopyGroup N X v,
      Work.Stems.Pinch.transport (N := N) (Work.Stems.Pinch.homotopyPath hH v) a = 1 := by
    intro a
    have h := Work.Stems.Pinch.transport_map (N := N) hH v a
    rw [HomotopyGroup.map_id] at h
    rw [h, hconst a]
  refine ⟨fun a a' => ?_⟩
  have h1a : a = Work.Stems.Pinch.transport (N := N)
      (Work.Stems.Pinch.homotopyPath hH v).symm 1 := by
    rw [← Work.Stems.Pinch.transport_symm_apply (N := N)
      (Work.Stems.Pinch.homotopyPath hH v) a, key a]
  have h1a' : a' = Work.Stems.Pinch.transport (N := N)
      (Work.Stems.Pinch.homotopyPath hH v).symm 1 := by
    rw [← Work.Stems.Pinch.transport_symm_apply (N := N)
      (Work.Stems.Pinch.homotopyPath hH v) a', key a']
  rw [h1a, h1a']

end Work.RatHurewicz.Cofibre

namespace Work.RatHurewicz.Cofibre

/-- **Bijectivity of the induced map on homotopy groups transfers along a homotopy**: homotopic maps
induce maps that differ by the base-point transport along the path traced by the homotopy
(`Work.Stems.Pinch.transport_map`). -/
theorem bijective_pimap_of_homotopic {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : f.Homotopy g) (n : ℕ) (x : X) :
    Function.Bijective (Work.StemsB.πmap f n x) → Function.Bijective (Work.StemsB.πmap g n x) := by
  intro hf
  have hfg : ∀ a : HomotopyGroup (Fin (n + 1)) X x,
      Work.Stems.Pinch.transport (N := Fin (n + 1)) (Work.Stems.Pinch.homotopyPath H x)
          (Work.StemsB.πmap f n x a)
        = Work.StemsB.πmap g n x a := by
    intro a
    rw [πmap_eq_map, πmap_eq_map]
    exact Work.Stems.Pinch.transport_map (N := Fin (n + 1)) H x a
  constructor
  · intro a b hab
    have h1 : Work.Stems.Pinch.transport (N := Fin (n + 1)) (Work.Stems.Pinch.homotopyPath H x)
          (Work.StemsB.πmap f n x a)
        = Work.Stems.Pinch.transport (N := Fin (n + 1)) (Work.Stems.Pinch.homotopyPath H x)
          (Work.StemsB.πmap f n x b) := by
      rw [hfg a, hfg b, hab]
    have h2 : Work.StemsB.πmap f n x a = Work.StemsB.πmap f n x b := by
      have h3 := congrArg (Work.Stems.Pinch.transport (N := Fin (n + 1))
        (Work.Stems.Pinch.homotopyPath H x).symm) h1
      rwa [Work.Stems.Pinch.transport_symm_apply, Work.Stems.Pinch.transport_symm_apply] at h3
    exact hf.1 h2
  · intro y
    obtain ⟨a, ha⟩ := hf.2 (Work.Stems.Pinch.transport (N := Fin (n + 1))
      (Work.Stems.Pinch.homotopyPath H x).symm y)
    refine ⟨a, ?_⟩
    rw [← hfg a, ha, Work.Stems.Pinch.transport_symm_apply']

end Work.RatHurewicz.Cofibre
