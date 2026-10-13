/-
  Subproject WilE9G / Assembly — the properties of `ambCatX`.

  `ambCatX S X` adjoins the chain of the semi-Pfaffian set `X` to the right of the chain of the
  ambient stratum `S` (keeping the *basics* of `S`, reindexed along `EAPoly.inl`).  It is the
  "chain-only" version of `ambCat`: the point set, the `Good` predicate, the `j`-equations and the
  degree of `S` are untouched, the format grows by `X.r`, the number of basics is unchanged, and a
  polynomial of `X`'s chain is evaluated inside the concatenation as before.
-/
import Mathlib
import Submission.Work.WilE9G.Assembly.Defs
import Submission.Work.WilE9G.Assembly.ambCat_set_good_deg

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE9G.Assembly
open WilkiesDesign WilkiesDesign.E

/-- The underlying point set of `ambCatX S X` is that of `S`: adjoining an unused chain to the
right does not change the DNF conditions, since `EAPoly.inl`-reindexed polynomials evaluate the
same in the concatenated chain. -/
theorem ambCatX_set {N : ℕ} (S : Work.WilE9G.AmbStratum N) (X : WilkiesDesign.E.SemiPf N) :
    (ambCatX S X).X.set = S.X.set := by
  ext z
  simp only [SemiPf.set, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hz, B, hB, hBh⟩
    obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.mp hB
    exact ⟨hz, B₀, hB₀,
      (Work.WilE7.SubPfAux.Basic.holds_cat_inl S.X.c X.c B₀ z).mp hBh⟩
  · rintro ⟨hz, B, hB, hBh⟩
    exact ⟨hz, Work.WilE7.Basic.inl B, List.mem_map_of_mem hB,
      (Work.WilE7.SubPfAux.Basic.holds_cat_inl S.X.c X.c B z).mpr hBh⟩

/-- The degree of `ambCatX S X` equals the degree of `S`: reindexing a basic condition along
`EAPoly.inl` preserves its degree. -/
theorem ambCatX_X_deg {N : ℕ} (S : Work.WilE9G.AmbStratum N) (X : WilkiesDesign.E.SemiPf N) :
    (ambCatX S X).X.deg = S.X.deg := by
  show ((S.X.basics.map Work.WilE7.Basic.inl).map Basic.deg).sum = S.X.deg
  rw [List.map_map, SemiPf.deg]
  exact congrArg List.sum
    (List.map_congr_left (fun B _ => Work.WilE9.Ift.OneShot.basic_deg_inl B))

/-- The `Good` predicate of `ambCatX S X` is that of `S`.  The equations and the Jacobian entries
are the same functions of the point, read in the concatenated chain. -/
theorem ambCatX_Good {N : ℕ} (S : Work.WilE9G.AmbStratum N) (X : WilkiesDesign.E.SemiPf N) :
    (ambCatX S X).Good ↔ S.Good := by
  have hset := ambCatX_set S X
  constructor
  · intro h z hz
    have hz' : z ∈ (ambCatX S X).X.set := by rw [hset]; exact hz
    have hh := h z hz'
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact (Work.WilE7.SubPfAux.eaEval_cat_inl S.X.c X.c (S.h a) z).symm.trans (hh.1 a)
    · have hmat : (Matrix.of fun (a : Fin S.j) (l : Fin N) =>
          eaEval (Work.WilE7.EAChain.cat S.X.c X.c)
            (eaD (Work.WilE7.EAChain.cat S.X.c X.c) l (Work.WilE7.EAPoly.inl (S.h a))) z) =
          (Matrix.of fun (a : Fin S.j) (l : Fin N) =>
            eaEval S.X.c (eaD S.X.c l (S.h a)) z) := by
        ext a l
        exact ambCat_jac_entry S X.c z a l
      have hmem : (Matrix.of fun (a : Fin S.j) (l : Fin N) =>
            eaEval (Work.WilE7.EAChain.cat S.X.c X.c)
              (eaD (Work.WilE7.EAChain.cat S.X.c X.c) l
                (Work.WilE7.EAPoly.inl (S.h a))) z).rank = S.j := hh.2.1
      rw [hmat] at hmem
      exact hmem
    · refine hh.2.2.mono ?_
      intro z' hz'' h0
      rw [← hset]
      exact hz'' (fun a =>
        (Work.WilE7.SubPfAux.eaEval_cat_inl S.X.c X.c (S.h a) z').trans (h0 a))
  · intro h z hz'
    have hz : z ∈ S.X.set := by rw [hset] at hz'; exact hz'
    have hh := h z hz
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact (Work.WilE7.SubPfAux.eaEval_cat_inl S.X.c X.c (S.h a) z).trans (hh.1 a)
    · have hmat : (Matrix.of fun (a : Fin S.j) (l : Fin N) =>
          eaEval (Work.WilE7.EAChain.cat S.X.c X.c)
            (eaD (Work.WilE7.EAChain.cat S.X.c X.c) l (Work.WilE7.EAPoly.inl (S.h a))) z) =
          (Matrix.of fun (a : Fin S.j) (l : Fin N) =>
            eaEval S.X.c (eaD S.X.c l (S.h a)) z) := by
        ext a l
        exact ambCat_jac_entry S X.c z a l
      have hmem : (Matrix.of fun (a : Fin S.j) (l : Fin N) =>
            eaEval S.X.c (eaD S.X.c l (S.h a)) z).rank = S.j := hh.2.1
      rw [← hmat] at hmem
      exact hmem
    · refine hh.2.2.mono ?_
      intro z' hz'' h0
      rw [hset]
      exact hz'' (fun a =>
        (Work.WilE7.SubPfAux.eaEval_cat_inl S.X.c X.c (S.h a) z').symm.trans (h0 a))

theorem ambCatX_props {N : ℕ} (S : Work.WilE9G.AmbStratum N) (X : WilkiesDesign.E.SemiPf N) :
    (Work.WilE9G.Assembly.ambCatX S X).X.set = S.X.set ∧
    ((Work.WilE9G.Assembly.ambCatX S X).Good ↔ S.Good) ∧
    (Work.WilE9G.Assembly.ambCatX S X).j = S.j ∧
    (Work.WilE9G.Assembly.ambCatX S X).X.fmt = S.X.fmt + X.r ∧
    (Work.WilE9G.Assembly.ambCatX S X).X.deg = S.X.deg ∧
    (Work.WilE9G.Assembly.ambCatX S X).deg = S.deg ∧
    (Work.WilE9G.Assembly.ambCatX S X).X.basics.length = S.X.basics.length ∧
    (∀ (Q : WilkiesDesign.E.EAPoly N X.r) (z : Fin N → ℝ),
        WilkiesDesign.E.eaEval (Work.WilE9G.Assembly.ambCatX S X).X.c
          (Work.WilE7.EAPoly.inr Q) z = WilkiesDesign.E.eaEval X.c Q z) := by
  refine ⟨ambCatX_set S X, ambCatX_Good S X, rfl, ?_, ambCatX_X_deg S X, ?_, ?_, ?_⟩
  · show N + (S.X.r + X.r) = S.X.fmt + X.r
    rw [SemiPf.fmt]
    omega
  · show (ambCatX S X).X.deg + (∑ a : Fin (ambCatX S X).j, atomDeg ((ambCatX S X).h a))
        = S.deg
    have hsum : (∑ a : Fin (ambCatX S X).j, atomDeg ((ambCatX S X).h a))
        = ∑ a : Fin S.j, atomDeg (S.h a) :=
      Finset.sum_congr rfl (fun a _ => Work.WilE9.Ift.OneShot.atomDeg_inl (S.h a))
    rw [hsum, ambCatX_X_deg, Work.WilE9G.AmbStratum.deg]
  · show (S.X.basics.map Work.WilE7.Basic.inl).length = S.X.basics.length
    simp
  · intro Q z
    exact Work.WilE7.SubPfAux.eaEval_cat_inr S.X.c X.c Q z

end Work.WilE9G.Assembly
