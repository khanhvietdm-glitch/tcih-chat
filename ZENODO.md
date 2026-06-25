# Getting a Zenodo DOI for this artefact

The repository ships citation metadata (`.zenodo.json`, `CITATION.cff`) so the
deposit is one form-fill away. Pick **one** path.

## Path A — GitHub ↔ Zenodo integration (easiest, auto-DOI on release)

1. Sign in at <https://zenodo.org> with your GitHub account.
2. Go to **Settings → GitHub** (<https://zenodo.org/account/settings/github/>)
   and flip the toggle **ON** for `khanhvietdm-glitch/tcih-chat`.
3. On GitHub, **publish a new release** (e.g. `v1.0.1`) — or re-publish `v1.0.0`.
   Zenodo automatically archives the repository source and mints a DOI; the
   metadata is taken from `.zenodo.json`.
4. *(Optional but recommended)* The auto-archive contains the **source only**,
   not the release asset. To include the full structure-only corpus, open the
   new Zenodo record → **New version** → upload
   `corpus_full_structure_only.tar.gz` (download it from the GitHub release) and
   `TCIH-Chat_ESWA_manuscript.docx`, then publish.

## Path B — Manual upload (full control over what the DOI archives)

1. <https://zenodo.org> → **New upload**.
2. Upload these files (the first is prepared in `zenodo_upload/`; the second is
   the GitHub release asset; the third is the manuscript):
   - `tcih-chat-v1.0.0-source.zip`
   - `corpus_full_structure_only.tar.gz`  (from the GitHub release v1.0.0)
   - `TCIH-Chat_ESWA_manuscript.docx`
3. Fill the form from `.zenodo.json`: title, authors + affiliations, license
   **MIT**, keywords; under **Related/alternate identifiers** add
   `https://github.com/khanhvietdm-glitch/tcih-chat` as *"is supplement to"*.
4. **Publish** → a DOI like `10.5281/zenodo.XXXXXXX` is minted.

## After you have the DOI

- Put it in the paper's *Data and code availability* statement (replace
  "archived on Zenodo with a citable DOI").
- Add a badge to `README.md`:
  `[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.XXXXXXX.svg)](https://doi.org/10.5281/zenodo.XXXXXXX)`
- Add the `version`/`doi` to `CITATION.cff`.

Tell me the DOI and I will insert it into the manuscript, README, and CITATION.cff.
