import Mathlib
import Submission.Work.DSCOH.ProdLocIsoBase
import Submission.Work.DSCOH.ChartFree
import Submission.Work.DSCOH.prodLocIso_divPow_toLoc
import Submission.Work.DSCOH.map_divPow_toLoc_shift_mono
import Submission.Work.DSCOH.iSup_iInf_comap_eq

namespace Work.DSCOH

/-

## The image of the degree-zero part of `∏_j S(-d_j)` under `prodLocIso`

`prodLocIso S r` identifies the localization at the chart `S` of the product
`∏_{j : Fin r} S(-d_j)` (presented as `Fin r → Poly A n` with the piecewise grading `freeGraded d`)
with the product of the localizations of the shifts.  This file proves that the degree-zero part
of the former is carried onto the product of the degree-zero parts of the latter:

`map ((prodLocIso S r).restrictScalars A) (degZero (freeGraded d) S) = degZeroProd d S`.

The two inclusions are read off from the explicit description of the `k`-th piece of `degZero`,
`map (divPow S k ∘ toLoc S) (ℳ (k·|S|))`:

* `prodLocIso` intertwines `divPow S k ∘ toLoc S` on the product with its coordinatewise
  counterpart on the shifts (`prodLocIso_divPow_toLoc`), so the image of the `k`-th piece of the
  product is the intersection, over `j`, of the `k`-th pieces of the shifts;
* those pieces are increasing in `k` (`map_divPow_toLoc_shift_mono`), so on a finite index set a
  supremum of intersections of increasing pieces is the intersection of the suprema
  (`iSup_iInf_comap_eq`).
-/

theorem map_prodLocIso_degZero {A : Type*} [CommRing A] {n : ℕ} {r : ℕ}
    (d : Fin r → ℕ) (S : Finset (Fin n)) :
    Submodule.map ((prodLocIso (A := A) (n := n) S r).restrictScalars A).toLinearMap
        (degZero (A := A) (n := n) (M := Fin r → Poly A n)
          (freeGraded (A := A) (n := n) d) S)
      = degZeroProd (A := A) (n := n) d S := by
  classical
  -- The `k`-th piece of the degree-zero part, transported along `prodLocIso`, is the product of
  -- the `k`-th pieces of the shifts.
  have hkey : ∀ k : ℕ,
      Submodule.map ((prodLocIso (A := A) (n := n) S r).restrictScalars A).toLinearMap
        (Submodule.map ((divPow (A := A) (n := n) (M := Fin r → Poly A n) S k).comp
            (toLoc (A := A) (n := n) (M := Fin r → Poly A n) S))
          (freeGraded (A := A) (n := n) d (k * S.card)))
      = ⨅ j, Submodule.comap
          ((LinearMap.proj (R := Poly A n)
            (φ := fun _ : Fin r => LocalizedModule (subS (A := A) S) (Poly A n)) j).restrictScalars A)
          (Submodule.map ((divPow (A := A) (n := n) (M := Poly A n) S k).comp
              (toLoc (A := A) (n := n) (M := Poly A n) S))
            (shift (A := A) (n := n) (d j) (k * S.card))) := by
    intro k
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
      obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy
      rw [← hyx, ← hzy]
      rw [Submodule.mem_iInf]
      intro j
      rw [Submodule.mem_comap]
      simp only [LinearMap.restrictScalars_apply, LinearMap.proj_apply]
      rw [Submodule.mem_map]
      refine ⟨z j, (mem_freeGraded.mp hz) j, ?_⟩
      have hcomp : ((prodLocIso (A := A) (n := n) S r).restrictScalars A).toLinearMap
          (((divPow (A := A) (n := n) (M := Fin r → Poly A n) S k).comp
            (toLoc (A := A) (n := n) (M := Fin r → Poly A n) S)) z)
          = fun j => ((divPow (A := A) (n := n) (M := Poly A n) S k).comp
            (toLoc (A := A) (n := n) (M := Poly A n) S)) (z j) :=
        prodLocIso_divPow_toLoc (A := A) (n := n) S k z
      rw [hcomp]
    · intro hx
      rw [Submodule.mem_iInf] at hx
      have hx' : ∀ j, x j ∈ Submodule.map ((divPow (A := A) (n := n) (M := Poly A n) S k).comp
            (toLoc (A := A) (n := n) (M := Poly A n) S))
          (shift (A := A) (n := n) (d j) (k * S.card)) := by
        intro j
        have h1 := hx j
        rw [Submodule.mem_comap] at h1
        simpa only [LinearMap.restrictScalars_apply, LinearMap.proj_apply] using h1
      choose nn hn hnx using fun j => Submodule.mem_map.mp (hx' j)
      rw [Submodule.mem_map]
      have hcomp : ((prodLocIso (A := A) (n := n) S r).restrictScalars A).toLinearMap
          (((divPow (A := A) (n := n) (M := Fin r → Poly A n) S k).comp
            (toLoc (A := A) (n := n) (M := Fin r → Poly A n) S)) (fun j => nn j))
          = fun j => ((divPow (A := A) (n := n) (M := Poly A n) S k).comp
            (toLoc (A := A) (n := n) (M := Poly A n) S)) (nn j) :=
        prodLocIso_divPow_toLoc (A := A) (n := n) S k (fun j => nn j)
      refine ⟨((divPow (A := A) (n := n) (M := Fin r → Poly A n) S k).comp
          (toLoc (A := A) (n := n) (M := Fin r → Poly A n) S)) (fun j => nn j), ?_, ?_⟩
      · exact Submodule.mem_map.mpr ⟨fun j => nn j, mem_freeGraded.mpr hn, rfl⟩
      · funext j
        rw [hcomp]
        exact hnx j
  unfold degZeroProd
  unfold degZero
  rw [Submodule.map_iSup]
  rw [show (⨆ k, Submodule.map ((prodLocIso (A := A) (n := n) S r).restrictScalars A).toLinearMap
        (Submodule.map ((divPow (A := A) (n := n) (M := Fin r → Poly A n) S k).comp
            (toLoc (A := A) (n := n) (M := Fin r → Poly A n) S))
          (freeGraded (A := A) (n := n) d (k * S.card))))
      = (⨆ k, ⨅ j, Submodule.comap
          ((LinearMap.proj (R := Poly A n)
            (φ := fun _ : Fin r => LocalizedModule (subS (A := A) S) (Poly A n)) j).restrictScalars A)
          (Submodule.map ((divPow (A := A) (n := n) (M := Poly A n) S k).comp
              (toLoc (A := A) (n := n) (M := Poly A n) S))
            (shift (A := A) (n := n) (d j) (k * S.card))))
      from iSup_congr fun k => hkey k]
  exact iSup_iInf_comap_eq
    (N := fun _ : Fin r => LocalizedModule (subS (A := A) S) (Poly A n))
    (g := fun j => (((LinearMap.proj (R := Poly A n)
      (φ := fun _ : Fin r => LocalizedModule (subS (A := A) S) (Poly A n)) j).restrictScalars A)
        : (Fin r → LocalizedModule (subS (A := A) S) (Poly A n)) →ₗ[A]
          LocalizedModule (subS (A := A) S) (Poly A n)))
    (D := fun k j => Submodule.map ((divPow (A := A) (n := n) (M := Poly A n) S k).comp
        (toLoc (A := A) (n := n) (M := Poly A n) S))
      (shift (A := A) (n := n) (d j) (k * S.card)))
    (fun j k k' h => map_divPow_toLoc_shift_mono (A := A) (n := n) (d j) (S := S) h)

end Work.DSCOH
