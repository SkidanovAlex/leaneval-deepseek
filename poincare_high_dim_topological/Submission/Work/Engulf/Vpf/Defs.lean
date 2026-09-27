import Submission.Work.Engulf.Vpf.Interp

/-!
# The vertex perturbation construction (`Work.Engulf.VertexPerturbForm`, contract §7.2)

`vpfC Z g y` is the new vertex data (`y` on `Z`, `g` off `Z`), `vpfA K c s` is the affine
interpolation of the vertex data `c` on the face `s` of `K`, and `vpfG' K Z g y` is the map
which on the union of the faces of `K` containing a `Z`-vertex is the affine interpolation of
the new vertex data and equals `g` elsewhere.  The lemmas below are the API used by
`Work.Engulf.Aux.vertexPerturbForm`.
-/

open Set Metric PL

namespace Work.Engulf.Vpf

variable {N n : ℕ}

/-! ## New vertex data -/

/-- The new vertex data: `y` on `Z`, `g` off `Z`. -/
noncomputable def vpfC (Z : Finset (E N)) (g y : E N → E n) : E N → E n := fun v => if v ∈ Z then y v else g v

theorem vpfC_apply_of_mem {Z : Finset (E N)} {g y : E N → E n} {v : E N} (hv : v ∈ Z) :
    vpfC Z g y v = y v := by
  simp [vpfC, hv]

theorem vpfC_apply_of_notMem {Z : Finset (E N)} {g y : E N → E n} {v : E N} (hv : v ∉ Z) :
    vpfC Z g y v = g v := by
  simp [vpfC, hv]

/-! ## Affine interpolation on a face -/

/-- The affine map interpolating the vertex data `c` on the face `s` (an arbitrary affine map
when `s` is not a face of `K`). -/
noncomputable def vpfA (K : Cx N) (c : E N → E n) (s : Finset (E N)) : E N →ᵃ[ℝ] E n := by
  classical
  exact if h : ∃ A : E N →ᵃ[ℝ] E n, ∀ v ∈ s, A v = c v then h.choose else 0

theorem vpfA_apply {K : Cx N} {c : E N → E n} {s : Finset (E N)} (hs : s ∈ K.faces) {v : E N}
    (hv : v ∈ s) : vpfA K c s v = c v := by
  have h : ∃ A : E N →ᵃ[ℝ] E n, ∀ v ∈ s, A v = c v := exists_affineMap_eqOn_of_mem_faces K c hs
  unfold vpfA
  rw [dite_eq_left h]
  exact h.choose_spec v hv

/-- Interpolations on two faces agree on the intersection of the simplices. -/
theorem vpfA_eqOn_inter {K : Cx N} {c : E N → E n} {s t : Finset (E N)}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    EqOn (vpfA K c s) (vpfA K c t) (simp s ∩ simp t) := by
  intro x hx
  rw [simp_inter hs ht] at hx
  exact eqOn_convexHull_of_eqOn_vertices
    (fun v hv => by
      obtain ⟨hvs, hvt⟩ := Finset.mem_inter.mp hv
      rw [vpfA_apply hs hvs, vpfA_apply ht hvt]) hx

/-! ## The perturbed map -/

/-- The perturbed map: on the union of the faces of `K` containing a `Z`-vertex it is the affine
interpolation of the new vertex data, elsewhere it is `g`. -/
noncomputable def vpfG' (K : Cx N) (Z : Finset (E N)) (g y : E N → E n) : E N → E n := by
  classical
  exact fun x => if h : ∃ s ∈ K.faces, (∃ v ∈ s, v ∈ Z) ∧ x ∈ simp s then
      vpfA K (vpfC Z g y) h.choose x
    else g x

theorem vpfG'_apply_of_mem {K : Cx N} {Z : Finset (E N)} {g y : E N → E n} {s : Finset (E N)}
    (hs : s ∈ K.faces) (hZ : ∃ v ∈ s, v ∈ Z) {x : E N} (hx : x ∈ simp s) :
    vpfG' K Z g y x = vpfA K (vpfC Z g y) s x := by
  have hh : ∃ s ∈ K.faces, (∃ v ∈ s, v ∈ Z) ∧ x ∈ simp s := ⟨s, hs, hZ, hx⟩
  unfold vpfG'
  rw [dite_eq_left hh]
  exact vpfA_eqOn_inter hh.choose_spec.1 hs ⟨hh.choose_spec.2.2, hx⟩

/-- `vpfG'` takes the prescribed value at the vertices of `Z`. -/
theorem vpfG'_apply_of_mem_Z {K : Cx N} {Z : Finset (E N)} {g y : E N → E n} {v : E N}
    (hZsub : ∀ v ∈ Z, ∃ s ∈ K.faces, v ∈ s) (hv : v ∈ Z) : vpfG' K Z g y v = y v := by
  obtain ⟨s, hs, hvs⟩ := hZsub v hv
  rw [vpfG'_apply_of_mem hs ⟨v, hvs, hv⟩ (subset_simp hvs), vpfA_apply hs hvs,
    vpfC_apply_of_mem hv]

end Work.Engulf.Vpf
