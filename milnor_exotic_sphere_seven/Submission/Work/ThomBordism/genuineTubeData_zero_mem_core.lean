import Mathlib
import Submission.Work.ThomBordism.genuineTubeData
import Submission.Work.ThomBordism.nonempty_genuineTubeData
import Submission.Work.PTGeometric.PadAmb
import Submission.Work.PTGeometric.TubeAmbient
import Submission.Work.PTGeometric.flatCoordAux
import Submission.Work.Tubular.Transversality
import Submission.Work.Tubular.Gauss
import Submission.Work.Tubular.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

/-- **The zero-set property of the concrete collapse, from the coordinate structure of the Thom
space.**

`hcore` says that the vector part of the ambient coordinates `coord` vanishes exactly on the `core`,
and `hcoord` identifies the ambient coordinates of the collapse `Work.Tubular.alphaV` with TUBULAR's
tube data (`Work.PTGeometric.tubeNormalProj`, `Work.PTGeometric.tubeNormalCoord`) at the points of
the open tube.  Since TUBULAR's normal coordinate vanishes exactly on the embedded piece
(`Work.Tubular.normalCoord_eq_zero_iff`) and the padding `padEuc` is injective, this gives the
`zero` field of `Work.PTGeometric.GenuineTubeGeometry` — the statement that the concrete collapse
lands in the core exactly over the embedded piece.  Off the open tube both sides are false: the
collapse is the basepoint there (`d.hg`) which is not in the core (`hcore0`), and the embedded piece
lies in the open tube (`Work.Tubular.TubeChart.mem_openTube`). -/
theorem genuineTubeData_zero_mem_core {V : Work.ThomBordism.Man8} {k : ℕ}
    {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {N : Work.ThomBordism.PontryaginThom.NormalBundlData V}
    (d : Work.ThomBordism.GenuineTubeData V k D N) {mU : ℕ} (hmU : 8 ≤ mU)
    (core : Set D.T) (hcore0 : D.t₀ ∉ core)
    (coord : {x : D.T // x ≠ D.t₀} →
      (EuclideanSpace ℝ (Fin (k + mU)) →L[ℝ] EuclideanSpace ℝ (Fin (k + mU))) ×
        EuclideanSpace ℝ (Fin (k + mU)))
    (hcore : ∀ x : {x : D.T // x ≠ D.t₀}, x.1 ∈ core ↔ (coord x).2 = 0)
    (hcoord : ∀ t : Fin (8 + k) → unitInterval,
      Work.Tubular.cubeToEuc (8 + k) d.R t ∈ d.chart.openTube →
      ∃ hne : Work.Tubular.alphaV d.chart d.hR d.hbox D.t₀ d.J d.hJ d.g d.hg t ≠ D.t₀,
        coord ⟨_, hne⟩ =
          (Work.PTGeometric.padEndEuc k mU hmU
              (Work.PTGeometric.tubeNormalProj d.emb d.chart
                (Work.Tubular.cubeToEuc (8 + k) d.R t)),
            Work.PTGeometric.padEuc k mU hmU
              (Work.PTGeometric.tubeNormalCoord d.emb d.chart
                (Work.Tubular.cubeToEuc (8 + k) d.R t)))) :
    ∀ t : Fin (8 + k) → unitInterval,
      Work.Tubular.alphaV d.chart d.hR d.hbox D.t₀ d.J d.hJ d.g d.hg t ∈ core ↔
        Work.Tubular.cubeToEuc (8 + k) d.R t ∈ Set.range d.emb.e := by
  intro t
  -- the padding is injective, so it detects the vanishing of the normal coordinate
  have hpad : ∀ v : EuclideanSpace ℝ (Fin (8 + k)),
      Work.PTGeometric.padEuc k mU hmU v = 0 ↔ v = 0 := by
    intro v
    constructor
    · intro h
      exact Work.PTGeometric.padEuc_injective k mU hmU (by rw [h, map_zero])
    · intro h; rw [h, map_zero]
  by_cases hmem : Work.Tubular.cubeToEuc (8 + k) d.R t ∈ d.chart.openTube
  · -- inside the open tube: read the coordinates off the collapse and use TUBULAR's zero locus
    obtain ⟨hne, hcoord_eq⟩ := hcoord t hmem
    calc Work.Tubular.alphaV d.chart d.hR d.hbox D.t₀ d.J d.hJ d.g d.hg t ∈ core
        ↔ (coord ⟨Work.Tubular.alphaV d.chart d.hR d.hbox D.t₀ d.J d.hJ d.g d.hg t, hne⟩).2 = 0 :=
          hcore ⟨_, hne⟩
      _ ↔ Work.PTGeometric.padEuc k mU hmU
            (Work.PTGeometric.tubeNormalCoord d.emb d.chart
              (Work.Tubular.cubeToEuc (8 + k) d.R t)) = 0 := by rw [hcoord_eq]
      _ ↔ Work.PTGeometric.tubeNormalCoord d.emb d.chart
            (Work.Tubular.cubeToEuc (8 + k) d.R t) = 0 := hpad _
      _ ↔ Work.Tubular.cubeToEuc (8 + k) d.R t ∈ Set.range d.emb.e :=
          Work.PTGeometric.tubeNormalCoord_eq_zero_iff d.emb d.chart hmem
  · -- off the open tube: the collapse is the basepoint, and the piece lies in the open tube
    have hnr : Work.Tubular.cubeToEuc (8 + k) d.R t ∉ Set.range d.emb.e := by
      rintro ⟨x, hx⟩
      rw [← hx] at hmem
      exact hmem (d.chart.mem_openTube x)
    have hav : Work.Tubular.alphaV d.chart d.hR d.hbox D.t₀ d.J d.hJ d.g d.hg t = D.t₀ := by
      show d.J (d.g (OnePoint.some (Work.Tubular.cubeToEuc (8 + k) d.R t))) = D.t₀
      rw [d.hg _ hmem, d.hJ]
    rw [hav]
    exact ⟨fun h => absurd h hcore0, fun h => absurd h hnr⟩

end Work.ThomBordism
