/-
  WilE8 — `*`-sets are closed under forgetting the last coordinate.

  If `Z ⊆ ℝ^{N+1}` is a `*`-set with format `≤ F` and degree `≤ D`, then so is the
  projection of `Z` onto its first `N` coordinates.  Both `Fin.init '' Z` and
  `WilkiesDesign.projLast Z` denote this projection (`Fin.init` and `projLast` agree on
  every set), so it suffices to prove the statement for `Fin.init '' Z` and transport.

  The proof is piecewise: `Star` is a union of `StarPiece`s; the `*`-piece obtained from
  `P : StarPiece (N+1)` by dropping the last coordinate is `Work.WilE7.StarPiece.init P`,
  whose underlying semi-Pfaffian set is the reindexing of `P.X` along the (value
  preserving) identification `(N+1)+m = N+(m+1)` and whose fibre dimension is `m+1`.
  Reindexing does not change the format or the degree (`totalDegree` is invariant under
  renamings along an equivalence), so the same list of pieces, `init`-ed, witnesses the
  claim.
-/
import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.reindex_component
import Submission.Work.WilE8.Basic

noncomputable section
open Classical Topology

namespace Work.WilE8.Star
open WilkiesDesign WilkiesDesign.E

/-! ## Reindexing preserves degrees -/

/-- `totalDegree` is invariant under `rename` along a bijection of the variables. -/
theorem totalDegree_rename_sumMap {k K r : ℕ} (e : Fin k ≃ Fin K) (Q : EAPoly k r) :
    (MvPolynomial.rename (Sum.map e id) Q).totalDegree = Q.totalDegree := by
  refine le_antisymm (MvPolynomial.totalDegree_rename_le _ Q) ?_
  have hcomp : (Sum.map e.symm id : Fin K ⊕ Fin r → Fin k ⊕ Fin r) ∘ Sum.map e id = id := by
    funext s
    rcases s with i | j <;> simp
  have h : MvPolynomial.rename (Sum.map e.symm id)
      (MvPolynomial.rename (Sum.map e id) Q) = Q := by
    rw [MvPolynomial.rename_rename, hcomp, MvPolynomial.rename_id_apply]
  calc Q.totalDegree
      = (MvPolynomial.rename (Sum.map e.symm id)
          (MvPolynomial.rename (Sum.map e id) Q)).totalDegree := by rw [h]
    _ ≤ (MvPolynomial.rename (Sum.map e id) Q).totalDegree :=
        MvPolynomial.totalDegree_rename_le _ _

/-- The degree of a single atom is unchanged by a reindexing. -/
theorem atomDeg_reindex {k K r : ℕ} (e : Fin k ≃ Fin K) (Q : EAPoly k r) :
    atomDeg (Work.WilE7.EAPoly.reindex e Q) = atomDeg Q := by
  simp only [atomDeg, Work.WilE7.EAPoly.reindex]
  rw [totalDegree_rename_sumMap]

/-- The degree of a basic set is unchanged by a reindexing. -/
theorem basic_reindex_deg {k K r : ℕ} (e : Fin k ≃ Fin K) (B : Basic k r) :
    Basic.deg (Work.WilE7.Basic.reindex e B) = Basic.deg B := by
  have h1 : B.eqs.map (atomDeg ∘ Work.WilE7.EAPoly.reindex e) = B.eqs.map atomDeg :=
    List.map_congr_left (fun Q _ => atomDeg_reindex e Q)
  have h2 : B.pos.map (atomDeg ∘ Work.WilE7.EAPoly.reindex e) = B.pos.map atomDeg :=
    List.map_congr_left (fun Q _ => atomDeg_reindex e Q)
  simp only [Basic.deg, Work.WilE7.Basic.reindex, List.map_append, List.map_map,
    List.sum_append, h1, h2]

/-- The degree of a semi-Pfaffian set is unchanged by a reindexing. -/
theorem semiPf_reindex_deg {k K : ℕ} (e : Fin k ≃ Fin K) (X : SemiPf k) :
    (Work.WilE7.SemiPf.reindex e X).deg = X.deg := by
  have h1 : X.basics.map (Basic.deg ∘ Work.WilE7.Basic.reindex e) = X.basics.map Basic.deg :=
    List.map_congr_left (fun B _ => basic_reindex_deg e B)
  simp only [SemiPf.deg, Work.WilE7.SemiPf.reindex, List.map_map, h1]

/-- The format of the `init`-ed piece is that of the original piece. -/
theorem init_fmt {N : ℕ} (P : StarPiece (N + 1)) :
    (Work.WilE7.StarPiece.init P).X.fmt = P.X.fmt := by
  change (N + (P.m + 1)) + P.X.r = P.X.fmt
  simp only [SemiPf.fmt]
  omega

/-- The degree of the `init`-ed piece is that of the original piece. -/
theorem init_deg {N : ℕ} (P : StarPiece (N + 1)) :
    (Work.WilE7.StarPiece.init P).X.deg = P.X.deg :=
  semiPf_reindex_deg _ P.X

/-! ## The `init`-ed piece -/

/-- The first `N` coordinates of `projFirst (N+1) m` of a reindexed point are the
first `N` coordinates of that point. -/
theorem init_projFirst {N m : ℕ} (e : Fin ((N + 1) + m) ≃ Fin (N + (m + 1)))
    (he : ∀ i : Fin ((N + 1) + m), (e i).val = i.val) (y : Fin (N + (m + 1)) → ℝ) :
    Fin.init (projFirst (N + 1) m (fun i => y (e i))) = projFirst N (m + 1) y := by
  funext j
  show y (e (Fin.castAdd m (Fin.castSucc j))) = y (Fin.castAdd (m + 1) j)
  congr 1
  refine Fin.ext ?_
  rw [he]
  simp

/-- Dropping the last coordinate of a `*`-piece is implemented by `StarPiece.init`. -/
theorem init_set {N : ℕ} (P : StarPiece (N + 1)) :
    (Work.WilE7.StarPiece.init P).set = Fin.init '' P.set := by
  have h₀ : (N + 1) + P.m = N + (P.m + 1) := by omega
  have he : ∀ i : Fin ((N + 1) + P.m), ((Work.WilE7.finEquiv h₀) i).val = i.val :=
    fun i => Work.WilE7.finEquiv_apply_val h₀ i
  have hC := Work.WilE7.reindex_component (Work.WilE7.finEquiv h₀) P.X P.p
  show projFirst N (P.m + 1) ''
        connectedComponentIn (Work.WilE7.SemiPf.reindex (Work.WilE7.finEquiv h₀) P.X).set
          (fun i => P.p ((Work.WilE7.finEquiv h₀).symm i))
      = Fin.init '' (projFirst (N + 1) P.m '' connectedComponentIn P.X.set P.p)
  rw [hC]
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rw [Set.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Set.mem_image]
    exact ⟨projFirst (N + 1) P.m (fun i => y (Work.WilE7.finEquiv h₀ i)),
      ⟨fun i => y (Work.WilE7.finEquiv h₀ i), hy, rfl⟩,
      init_projFirst (N := N) (m := P.m) (Work.WilE7.finEquiv h₀) he y⟩
  · intro x hx
    rw [Set.mem_image] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    rw [Set.mem_image] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    rw [Set.mem_image]
    refine ⟨fun j => z ((Work.WilE7.finEquiv h₀).symm j), ?_, ?_⟩
    · have h2 : (fun i => (fun j => z ((Work.WilE7.finEquiv h₀).symm j))
            ((Work.WilE7.finEquiv h₀) i)) = z := by funext i; simp
      change (fun i => (fun j => z ((Work.WilE7.finEquiv h₀).symm j))
            ((Work.WilE7.finEquiv h₀) i)) ∈ connectedComponentIn P.X.set P.p
      rw [h2]
      exact hz
    · rw [← init_projFirst (N := N) (m := P.m) (Work.WilE7.finEquiv h₀) he
            (fun j => z ((Work.WilE7.finEquiv h₀).symm j))]
      have h2 : (fun i => (fun j => z ((Work.WilE7.finEquiv h₀).symm j))
            ((Work.WilE7.finEquiv h₀) i)) = z := by funext i; simp
      rw [h2]

/-! ## The main statement -/

theorem init_star {N F D : ℕ} {Z : Set (Fin (N + 1) → ℝ)}
    (h : WilkiesDesign.E.Star F D (N + 1) Z) :
    WilkiesDesign.E.Star F D N (Fin.init '' Z) ∧
      WilkiesDesign.E.Star F D N (WilkiesDesign.projLast Z) := by
  obtain ⟨L, hZ, hfmt, hdeg⟩ := h
  have hmain : WilkiesDesign.E.Star F D N (Fin.init '' Z) := by
    refine ⟨L.map Work.WilE7.StarPiece.init, ?_, ?_, ?_⟩
    · rw [hZ]
      ext x
      constructor
      · intro hx
        rw [Set.mem_image] at hx
        obtain ⟨z, hz, rfl⟩ := hx
        rw [Work.WilE8.mem_list_iUnion] at hz
        obtain ⟨P, hP, hzP⟩ := hz
        rw [Work.WilE8.mem_list_iUnion]
        exact ⟨Work.WilE7.StarPiece.init P, List.mem_map.mpr ⟨P, hP, rfl⟩,
          by rw [init_set P]; exact ⟨z, hzP, rfl⟩⟩
      · intro hx
        rw [Work.WilE8.mem_list_iUnion] at hx
        obtain ⟨Q, hQ, hxQ⟩ := hx
        obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hQ
        rw [init_set P] at hxQ
        obtain ⟨z, hzP, rfl⟩ := hxQ
        rw [Set.mem_image]
        exact ⟨z, by rw [Work.WilE8.mem_list_iUnion]; exact ⟨P, hP, hzP⟩, rfl⟩
    · intro Q hQ
      obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hQ
      rw [init_fmt P]
      exact hfmt P hP
    · have hmc : ((L.map Work.WilE7.StarPiece.init).map (fun Q : StarPiece N => Q.X.deg))
          = L.map (fun P : StarPiece (N + 1) => P.X.deg) := by
        rw [List.map_map]
        exact List.map_congr_left (fun P _ => init_deg P)
      rw [hmc]
      exact hdeg
  have hproj : WilkiesDesign.projLast Z = Fin.init '' Z := by
    ext x
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨Fin.snoc x t, ht, by simp⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z (Fin.last N), by rw [Fin.snoc_init_self z]; exact hz⟩
  exact ⟨hmain, by rw [hproj]; exact hmain⟩

end Work.WilE8.Star
